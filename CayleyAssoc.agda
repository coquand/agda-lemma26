{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Free associativity/unit reassociation of ∙-composites, via the Yoneda
-- (Cayley) embedding p ↦ (p ∙_).  Composition of the embedded maps is
-- function composition, which is STRICTLY (definitionally) associative and
-- unital — so any two bracketings of the same atom sequence have the same
-- Cayley image up to `refl`, and `solveR` turns the reassociation proof
-- into `refl`.  Pure Spartan: no funext, no new features, no datatypes
-- beyond a tiny expression syntax.
--
-- (Inverse cancellation is NOT free — that is a genuine groupoid relation,
-- handled separately by cancL/cancR.  This solver replaces the pure
-- reassociation grind: fa4..fa7, push6, etc.)
------------------------------------------------------------------------

module CayleyAssoc where

open import Spartan

module _ {A : Type 𝓤} where

  -- expression syntax: atoms are literal paths, ⊕ is ∙, ε is refl
  data Expr : A → A → Type 𝓤 where
    ι   : {a b : A} → a ≡ b → Expr a b
    ε   : {a : A} → Expr a a
    _⊕_ : {a b c : A} → Expr a b → Expr b c → Expr a c

  infixr 5 _⊕_

  eval : {a b : A} → Expr a b → a ≡ b
  eval (ι p)   = p
  eval ε       = refl _
  eval (x ⊕ y) = eval x ∙ eval y

  -- the Cayley image:  D E z k = eval E ∙ k, but built by ∘ so that
  -- associativity/units are definitional.
  D : {a b : A} → Expr a b → (z : A) → b ≡ z → a ≡ z
  D (ι p)   z k = p ∙ k
  D ε       z k = k
  D (x ⊕ y) z k = D x z (D y z k)

  D-correct : {a b : A} (E : Expr a b) (z : A) (k : b ≡ z) → D E z k ≡ eval E ∙ k
  D-correct (ι p)   z k = refl _
  D-correct ε       z k = refl _
  D-correct (x ⊕ y) z k =
      ap (D x z) (D-correct y z k)
    ∙ D-correct x z (eval y ∙ k)
    ∙ (∙-assoc (eval x) (eval y) k) ⁻¹

  -- the solver: if the two Cayley images agree at refl (which holds by `refl`
  -- whenever the expressions differ only by bracketing / units), the
  -- denotations are equal.
  solveR : {a b : A} (E1 E2 : Expr a b)
         → D E1 b (refl b) ≡ D E2 b (refl b)
         → eval E1 ≡ eval E2
  solveR {a} {b} E1 E2 h =
      (right-unit (eval E1)) ⁻¹
    ∙ (D-correct E1 b (refl b)) ⁻¹
    ∙ h
    ∙ D-correct E2 b (refl b)
    ∙ right-unit (eval E2)

------------------------------------------------------------------------
-- test: a nontrivial reassociation closes by `solveR _ _ (refl _)`
------------------------------------------------------------------------

private
  test : {A : Type 𝓤} {a b c d e : A}
         (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
       → ((p ∙ q) ∙ r) ∙ s ≡ p ∙ (q ∙ (r ∙ s))
  test p q r s =
    solveR (((ι p ⊕ ι q) ⊕ ι r) ⊕ ι s)
           (ι p ⊕ (ι q ⊕ (ι r ⊕ ι s)))
           (refl _)

  -- units are absorbed too
  test-unit : {A : Type 𝓤} {a b c : A} (p : a ≡ b) (q : b ≡ c)
            → (p ∙ refl b) ∙ q ≡ p ∙ q
  test-unit p q =
    solveR ((ι p ⊕ ε) ⊕ ι q) (ι p ⊕ ι q) (refl _)
