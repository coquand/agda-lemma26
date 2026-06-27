{-# OPTIONS --without-K --exact-split #-}

module Category.Pullbacks where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.Constructions

------------------------------------------------------------------------
-- Equivalence inverse: right and left inverse laws
------------------------------------------------------------------------

equiv-inv-rinv : {A : Type 𝓤} {B : Type 𝓥} (e : A ≃ B) (b : B)
               → pr₁ e (equiv-inv e b) ≡ b
equiv-inv-rinv (f , ef) b = pr₂ (center (ef b))

equiv-inv-linv : {A : Type 𝓤} {B : Type 𝓥} (e : A ≃ B) (a : A)
               → equiv-inv e (pr₁ e a) ≡ a
equiv-inv-linv (f , ef) a = ap pr₁ (centrality (ef (f a)) (a , refl (f a)))

------------------------------------------------------------------------
-- Transport over a constant family is the identity
------------------------------------------------------------------------

transport-const : {A : Type 𝓤} {B : Type 𝓥} {x y : A}
                → (p : x ≡ y) (b : B) → transport (λ _ → B) p b ≡ b
transport-const (refl _) b = refl b

------------------------------------------------------------------------
-- Cones for pullback diagrams
------------------------------------------------------------------------

Cone : {B A C : Cat} → Map B A → Map C A → Cat → Type 𝓤₀
Cone {B} {A} {C} f g X =
  Σ h ꞉ Map X B , Σ k ꞉ Map X C , comp f h ≡ comp g k

------------------------------------------------------------------------
-- Axiom 13: Cat has pullbacks
------------------------------------------------------------------------

postulate
  pb      : {B A C : Cat} → Map B A → Map C A → Cat
  pb-pr₁  : {B A C : Cat} (f : Map B A) (g : Map C A)
           → Map (pb f g) B
  pb-pr₂  : {B A C : Cat} (f : Map B A) (g : Map C A)
           → Map (pb f g) C
  pb-comm : {B A C : Cat} (f : Map B A) (g : Map C A)
           → comp f (pb-pr₁ f g) ≡ comp g (pb-pr₂ f g)

pb-comparison : {B A C : Cat} (f : Map B A) (g : Map C A) (X : Cat)
              → Map X (pb f g) → Cone f g X
pb-comparison f g X u =
  comp (pb-pr₁ f g) u ,
  comp (pb-pr₂ f g) u ,
  comp-assoc f (pb-pr₁ f g) u
  ∙ ap (λ m → comp m u) (pb-comm f g)
  ∙ (comp-assoc g (pb-pr₂ f g) u) ⁻¹

postulate
  pb-is-equiv : {B A C : Cat} (f : Map B A) (g : Map C A) (X : Cat)
              → is-equiv (pb-comparison f g X)

pb-equiv : {B A C : Cat} (f : Map B A) (g : Map C A) (X : Cat)
         → Map X (pb f g) ≃ Cone f g X
pb-equiv f g X = pb-comparison f g X , pb-is-equiv f g X

------------------------------------------------------------------------
-- Remark 14: Binary products
--
-- The product A ×c B is the pullback of  A →! 𝟏c ←! B.
-- Since Map(X, 𝟏c) is contractible, the commutativity condition
-- in the cone is automatic, giving Map(X, A ×c B) ≃ Map(X,A) × Map(X,B).
------------------------------------------------------------------------

_×c_ : Cat → Cat → Cat
A ×c B = pb (! A) (! B)

infixr 2 _×c_

π₁ : (A B : Cat) → Map (A ×c B) A
π₁ A B = pb-pr₁ (! A) (! B)

π₂ : (A B : Cat) → Map (A ×c B) B
π₂ A B = pb-pr₂ (! A) (! B)

-- Pairing: given h : X → A and k : X → B, build ⟨h,k⟩ : X → A ×c B

⟨_,_⟩ : {A B X : Cat} → Map X A → Map X B → Map X (A ×c B)
⟨_,_⟩ {A} {B} {X} h k =
  equiv-inv (pb-equiv (! A) (! B) X)
    (h , k , singletons-are-props (terminal X) (comp (! A) h) (comp (! B) k))

-- β₁: comp π₁ ⟨h,k⟩ ≡ h

pair-β₁ : {A B X : Cat} (h : Map X A) (k : Map X B)
         → comp (π₁ A B) ⟨ h , k ⟩ ≡ h
pair-β₁ {A} {B} {X} h k =
  ap pr₁ (equiv-inv-rinv (pb-equiv (! A) (! B) X) cone)
  where
    cone : Cone (! A) (! B) X
    cone = h , k , singletons-are-props (terminal X) _ _

-- β₂: comp π₂ ⟨h,k⟩ ≡ k

pair-β₂ : {A B X : Cat} (h : Map X A) (k : Map X B)
         → comp (π₂ A B) ⟨ h , k ⟩ ≡ k
pair-β₂ {A} {B} {X} h k =
  ap (λ c → pr₁ (pr₂ c)) (equiv-inv-rinv (pb-equiv (! A) (! B) X) cone)
  where
    cone : Cone (! A) (! B) X
    cone = h , k , singletons-are-props (terminal X) _ _

-- η: ⟨ comp π₁ u , comp π₂ u ⟩ ≡ u

pair-η : {A B X : Cat} (u : Map X (A ×c B))
       → ⟨ comp (π₁ A B) u , comp (π₂ A B) u ⟩ ≡ u
pair-η {A} {B} {X} u =
  ap (equiv-inv e) cone-path ∙ equiv-inv-linv e u
  where
    e = pb-equiv (! A) (! B) X
    cone' : Cone (! A) (! B) X
    cone' = comp (π₁ A B) u , comp (π₂ A B) u ,
            singletons-are-props (terminal X) _ _
    cone-path : cone' ≡ pb-comparison (! A) (! B) X u
    cone-path = to-Σ-≡ (refl _ ,
                  to-Σ-≡ (refl _ ,
                    props-are-sets (singletons-are-props (terminal X)) _ _ _ _))

-- The product universal property as an equivalence

prod-comparison : (A B X : Cat) → Map X (A ×c B) → Map X A × Map X B
prod-comparison A B X u = comp (π₁ A B) u , comp (π₂ A B) u

prod-section : (A B X : Cat) → Map X A × Map X B → Map X (A ×c B)
prod-section A B X (h , k) = ⟨ h , k ⟩

prod-roundtrip : (A B X : Cat) (p : Map X A × Map X B)
               → prod-comparison A B X (prod-section A B X p) ≡ p
prod-roundtrip A B X (h , k) =
  to-Σ-≡ (pair-β₁ h k , transport-const (pair-β₁ h k) _ ∙ pair-β₂ h k)

-- NOTE: the former `pb-eq` (collapsing two cones with equal legs via
-- `map-is-set`) was removed: with `Map A B` no longer a set the
-- compatibility 2-cell is genuine data, so that statement is false in
-- general.  It was dead code (no live file used it).
