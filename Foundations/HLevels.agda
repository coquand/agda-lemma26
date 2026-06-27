{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- h-level helpers for the posetal development (Stream A, Lemma 26).
--
-- The workhorse is `hedberg-set`: a type carrying a reflexive,
-- prop-valued relation that implies identity is a set.  Everything
-- else (sets are closed under equivalence and binary sums, 𝟚 and Ord n
-- are sets, hence Ob 𝕀 and Ob (Δ n) are sets) follows from it.
------------------------------------------------------------------------

module Foundations.HLevels where

open import Foundations.Spartan
open import Category.HigherCat using (𝟚; 𝕀; 𝕀-ob; equiv-inj)
open import Category.CatAxioms using (Cat; Ob)
open import Interval.Interval using (Δ; Ord; construction-20)

------------------------------------------------------------------------
-- Path-algebra helper
------------------------------------------------------------------------

-- a ⁻¹ ∙ (a ∙ p) ≡ p
inv-cancel-l : {A : Type 𝓤} {x y : A} (a : x ≡ x) (p : x ≡ y)
  → a ⁻¹ ∙ (a ∙ p) ≡ p
inv-cancel-l a p =
  (∙-assoc (a ⁻¹) a p) ⁻¹ ∙ ap (λ r → r ∙ p) (left-inv a)

------------------------------------------------------------------------
-- Hedberg-style: a reflexive prop-valued relation that detects identity
-- makes a type a set.
------------------------------------------------------------------------

hedberg-set : {X : Type 𝓤} (R : X → X → Type 𝓥)
  → ((x y : X) → is-prop (R x y))
  → ((x : X) → R x x)
  → ((x y : X) → R x y → x ≡ y)
  → is-set X
hedberg-set {X = X} R Rprop ρ f x y p q =
  lemma p ∙ ap (λ r → c ⁻¹ ∙ r) (ap (f x y) (Rprop x y (enc p) (enc q)))
        ∙ (lemma q) ⁻¹
  where
    c : x ≡ x
    c = f x x (ρ x)
    enc : {a b : X} → a ≡ b → R a b
    enc {a} pa = transport (R a) pa (ρ a)
    KEY : (a b : X) (pa : a ≡ b) → f a b (enc pa) ≡ f a a (ρ a) ∙ pa
    KEY a a (refl a) = (right-unit (f a a (ρ a))) ⁻¹
    lemma : (pa : x ≡ y) → pa ≡ c ⁻¹ ∙ f x y (enc pa)
    lemma pa = (inv-cancel-l c pa) ⁻¹ ∙ ap (λ r → c ⁻¹ ∙ r) ((KEY x y pa) ⁻¹)

------------------------------------------------------------------------
-- Sets are closed under equivalence (preimage direction)
------------------------------------------------------------------------

equiv-is-set : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → is-set B → is-set A
equiv-is-set e sB = hedberg-set R Rprop ρ dec
  where
    f = pr₁ e
    R : _ → _ → Type _
    R a a' = f a ≡ f a'
    Rprop : (a a' : _) → is-prop (R a a')
    Rprop a a' = sB (f a) (f a')
    ρ : (a : _) → R a a
    ρ a = refl (f a)
    dec : (a a' : _) → R a a' → a ≡ a'
    dec a a' r = equiv-inj f (pr₂ e) r

------------------------------------------------------------------------
-- 𝟘, 𝟙, binary sums, 𝟚, Ord n are sets
------------------------------------------------------------------------

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop x _ = 𝟘-elim x

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop = 𝟙-induction (λ x → (y : 𝟙) → x ≡ y)
              (𝟙-induction (λ y → ⋆ ≡ y) (refl ⋆))

𝟙-is-set : is-set 𝟙
𝟙-is-set = props-are-sets 𝟙-is-prop

×-is-prop : {A B : Type 𝓤} → is-prop A → is-prop B → is-prop (A × B)
×-is-prop pA pB (a , b) (a' , b') = to-Σ-≡ (pA a a' , pB _ b')

-- a function into a set is a set, and a Σ with set base + prop fibres is a
-- set (both via Hedberg, avoiding any need for funext-as-equivalence)
fn-into-set : {A : Type 𝓤} {B : Type 𝓥} → is-set B → is-set (A → B)
fn-into-set {A = A} {B} sB = hedberg-set R Rprop ρ dec
  where
    R : (A → B) → (A → B) → Type _
    R f g = (a : A) → f a ≡ g a
    Rprop : (f g : A → B) → is-prop (R f g)
    Rprop f g = Π-is-prop (λ a → sB (f a) (g a))
    ρ : (f : A → B) → R f f
    ρ f a = refl (f a)
    dec : (f g : A → B) → R f g → f ≡ g
    dec f g e = funext e

Σ-set-prop : {A : Type 𝓤} {P : A → Type 𝓥}
  → is-set A → ((a : A) → is-prop (P a)) → is-set (Σ P)
Σ-set-prop {P = P} sA Pprop = hedberg-set
  (λ w w' → pr₁ w ≡ pr₁ w')
  (λ w w' → sA (pr₁ w) (pr₁ w'))
  (λ w → refl (pr₁ w))
  (λ w w' e → to-Σ-≡ (e , Pprop (pr₁ w') _ (pr₂ w')))

------------------------------------------------------------------------
-- Contractibility helpers (for the 𝟏c base of Delta-posetal)
------------------------------------------------------------------------

-- a function into a contractible type is contractible
fn-into-contr-is-contr : {A : Type 𝓤} {B : Type 𝓥}
  → is-contr B → is-contr (A → B)
fn-into-contr-is-contr cB =
  (λ _ → center cB) , (λ g → funext (λ a → centrality cB (g a)))

-- a Σ over a contractible base with prop fibres, with a global section, is
-- contractible
Σ-prop-contr : {A : Type 𝓤} {P : A → Type 𝓥}
  → (cA : is-contr A) → ((a : A) → is-prop (P a)) → ((a : A) → P a)
  → is-contr (Σ P)
Σ-prop-contr {P = P} cA Pprop sec =
  (center cA , sec (center cA)) ,
  (λ w → to-Σ-≡ (centrality cA (pr₁ w) , Pprop (pr₁ w) _ (pr₂ w)))

+-is-set : {A B : Type 𝓤₀} → is-set A → is-set B → is-set (A + B)
+-is-set {A = A} {B = B} sA sB = hedberg-set code cprop crefl cdec
  where
    code : A + B → A + B → Type 𝓤₀
    code (inl a) (inl a') = a ≡ a'
    code (inl _) (inr _) = 𝟘
    code (inr _) (inl _) = 𝟘
    code (inr b) (inr b') = b ≡ b'
    cprop : (x y : A + B) → is-prop (code x y)
    cprop (inl a) (inl a') = sA a a'
    cprop (inl _) (inr _) = 𝟘-is-prop
    cprop (inr _) (inl _) = 𝟘-is-prop
    cprop (inr b) (inr b') = sB b b'
    crefl : (x : A + B) → code x x
    crefl (inl a) = refl a
    crefl (inr b) = refl b
    cdec : (x y : A + B) → code x y → x ≡ y
    cdec (inl a) (inl a') p = ap inl p
    cdec (inl _) (inr _) ()
    cdec (inr _) (inl _) ()
    cdec (inr b) (inr b') p = ap inr p

𝟚-is-set : is-set 𝟚
𝟚-is-set = +-is-set 𝟙-is-set 𝟙-is-set

Ord-is-set : (n : ℕ) → is-set (Ord n)
Ord-is-set zero    = 𝟙-is-set
Ord-is-set (suc n) = +-is-set (Ord-is-set n) 𝟙-is-set

------------------------------------------------------------------------
-- Objects of the simplices are sets
------------------------------------------------------------------------

ob-𝕀-is-set : is-set (Ob 𝕀)
ob-𝕀-is-set = equiv-is-set 𝕀-ob 𝟚-is-set

ob-Δ-is-set : (n : ℕ) → is-set (Ob (Δ n))
ob-Δ-is-set n = equiv-is-set (construction-20 n) (Ord-is-set n)
