{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- A free-GROUPOID solver for `_∙_` / `_⁻¹`, extending `CayleyAssoc`.
--
-- `CayleyAssoc.solveR` makes ASSOCIATIVITY and UNITS of `_∙_` free, via the
-- Yoneda/Cayley embedding p ↦ (p ∙_): function composition is strictly
-- associative and unital, so any two bracketings give the same Cayley image
-- up to `refl`.  This module adds INVERSES to that embedding.  The Cayley
-- action `D`/`Dinv` pushes `_⁻¹` all the way to the atoms, so that
--
--     • associativity                (p ∙ q) ∙ r  =  p ∙ (q ∙ r)
--     • units                        p ∙ refl     =  p
--     • inverse-of-composite         (p ∙ q) ⁻¹   =  q ⁻¹ ∙ p ⁻¹
--     • double-inverse               (p ⁻¹) ⁻¹    =  p
--     • inverse-of-unit              refl ⁻¹      =  refl
--
-- all become DEFINITIONAL on the Cayley side, so a goal that differs only by
-- these laws closes by `solveG _ _ (refl _)`.
--
-- NOT free (a genuine groupoid relation needing the actual atom, not just its
-- shape): inverse CANCELLATION  p ∙ p ⁻¹ = refl.  Use `cancL`/`cancR` for it.
--
-- Pure Spartan: no funext, no reflection, no postulates.  `ap` is handled by
-- treating each `ap f p` as an opaque atom (the goal lives in one type).
------------------------------------------------------------------------

module GroupoidSolver where

open import Spartan

module _ {A : Type 𝓤} where

  -- expression syntax: atoms, refl (ε), composition (⊕), inverse (inv).
  data Expr : A → A → Type 𝓤 where
    ι   : {a b : A} → a ≡ b → Expr a b
    ε   : {a : A} → Expr a a
    _⊕_ : {a b c : A} → Expr a b → Expr b c → Expr a c
    inv : {a b : A} → Expr a b → Expr b a

  infixr 5 _⊕_

  eval : {a b : A} → Expr a b → a ≡ b
  eval (ι p)   = p
  eval ε       = refl _
  eval (x ⊕ y) = eval x ∙ eval y
  eval (inv x) = (eval x) ⁻¹

  ------------------------------------------------------------------------
  -- The Cayley action and its inverse co-action, mutually defined so that
  --   D    E z k = eval E ∙ k        (forwards)
  --   Dinv E z k = (eval E) ⁻¹ ∙ k   (backwards)
  -- are built by ∘ — pushing both composition AND inversion to the atoms.
  ------------------------------------------------------------------------

  D    : {a b : A} → Expr a b → (z : A) → b ≡ z → a ≡ z
  Dinv : {a b : A} → Expr a b → (z : A) → a ≡ z → b ≡ z

  D (ι p)   z k = p ∙ k
  D ε       z k = k
  D (x ⊕ y) z k = D x z (D y z k)
  D (inv x) z k = Dinv x z k

  Dinv (ι p)   z k = p ⁻¹ ∙ k
  Dinv ε       z k = k
  Dinv (x ⊕ y) z k = Dinv y z (Dinv x z k)
  Dinv (inv x) z k = D x z k

  ------------------------------------------------------------------------
  -- Soundness of the two actions, by mutual induction.
  ------------------------------------------------------------------------

  -- local groupoid facts (kept self-contained — Spartan only).
  inv-inv : {a b : A} (p : a ≡ b) → (p ⁻¹) ⁻¹ ≡ p
  inv-inv (refl _) = refl _

  ∙inv : {a b c : A} (p : a ≡ b) (q : b ≡ c) → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
  ∙inv (refl _) q = (right-unit (q ⁻¹)) ⁻¹

  D-correct    : {a b : A} (E : Expr a b) (z : A) (k : b ≡ z)
               → D E z k ≡ eval E ∙ k
  Dinv-correct : {a b : A} (E : Expr a b) (z : A) (k : a ≡ z)
               → Dinv E z k ≡ (eval E) ⁻¹ ∙ k

  D-correct (ι p)   z k = refl _
  D-correct ε       z k = refl _
  D-correct (x ⊕ y) z k =
      ap (D x z) (D-correct y z k)
    ∙ D-correct x z (eval y ∙ k)
    ∙ (∙-assoc (eval x) (eval y) k) ⁻¹
  D-correct (inv x) z k = Dinv-correct x z k

  Dinv-correct (ι p)   z k = refl _
  Dinv-correct ε       z k = refl _
  Dinv-correct (x ⊕ y) z k =
      Dinv-correct y z (Dinv x z k)
    ∙ ap (λ w → (eval y) ⁻¹ ∙ w) (Dinv-correct x z k)
    ∙ (∙-assoc ((eval y) ⁻¹) ((eval x) ⁻¹) k) ⁻¹
    ∙ ap (λ w → w ∙ k) ((∙inv (eval x) (eval y)) ⁻¹)
  Dinv-correct (inv x) z k =
      D-correct x z k
    ∙ ap (λ w → w ∙ k) ((inv-inv (eval x)) ⁻¹)

  ------------------------------------------------------------------------
  -- The solver: two expressions with equal Cayley image (at refl) have
  -- equal denotations.  In practice the hypothesis is `refl _` whenever the
  -- two sides differ only by assoc / units / inverse-distribution / inv-inv.
  ------------------------------------------------------------------------

  solveG : {a b : A} (E1 E2 : Expr a b)
         → D E1 b (refl b) ≡ D E2 b (refl b)
         → eval E1 ≡ eval E2
  solveG {a} {b} E1 E2 h =
      (right-unit (eval E1)) ⁻¹
    ∙ (D-correct E1 b (refl b)) ⁻¹
    ∙ h
    ∙ D-correct E2 b (refl b)
    ∙ right-unit (eval E2)

  ------------------------------------------------------------------------
  -- Genuine groupoid cancellation (NOT free): needs the shared atom.
  ------------------------------------------------------------------------

  cancL : {a b c : A} (p : a ≡ b) (q : b ≡ c) → p ⁻¹ ∙ (p ∙ q) ≡ q
  cancL (refl _) q = refl q

  cancR : {a b c : A} (p : a ≡ b) (q : c ≡ a) → (q ∙ p) ∙ p ⁻¹ ≡ q
  cancR (refl _) q = right-unit (q ∙ refl _) ∙ right-unit q

------------------------------------------------------------------------
-- Tests: each closes by `solveG _ _ (refl _)`.
------------------------------------------------------------------------

private
  -- pure reassociation (as in CayleyAssoc)
  test-assoc : {A : Type 𝓤} {a b c d e : A}
       (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
     → ((p ∙ q) ∙ r) ∙ s ≡ p ∙ (q ∙ (r ∙ s))
  test-assoc p q r s =
    solveG (((ι p ⊕ ι q) ⊕ ι r) ⊕ ι s)
           (ι p ⊕ (ι q ⊕ (ι r ⊕ ι s)))
           (refl _)

  -- inverse-of-composite distributes (and reassociates) for free
  test-inv-dist : {A : Type 𝓤} {a b c d : A}
       (p : a ≡ b) (q : b ≡ c) (r : a ≡ d)
     → (p ∙ q) ⁻¹ ∙ r ≡ q ⁻¹ ∙ (p ⁻¹ ∙ r)
  test-inv-dist p q r =
    solveG (inv (ι p ⊕ ι q) ⊕ ι r)
           (inv (ι q) ⊕ (inv (ι p) ⊕ ι r))
           (refl _)

  -- double inverse collapses for free
  test-inv-inv : {A : Type 𝓤} {a b : A} (p : a ≡ b)
     → (p ⁻¹) ⁻¹ ≡ p
  test-inv-inv p = solveG (inv (inv (ι p))) (ι p) (refl _)

  -- mixed: units, inverse-of-composite, double inverse, reassociation
  test-mixed : {A : Type 𝓤} {a b c : A} (p : a ≡ b) (q : b ≡ c)
     → ((p ∙ refl _) ∙ q) ⁻¹ ≡ q ⁻¹ ∙ ((p ⁻¹ ⁻¹) ⁻¹ ∙ refl _)
  test-mixed p q =
    solveG (inv ((ι p ⊕ ε) ⊕ ι q))
           (inv (ι q) ⊕ (inv (inv (inv (ι p))) ⊕ ε))
           (refl _)
