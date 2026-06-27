{-# OPTIONS --without-K --exact-split #-}

module Exponentials where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks

------------------------------------------------------------------------
-- Axiom 15: Cat has exponential objects
--
-- For A B : Cat, we postulate Fun(A, B) with evaluation
-- ev : Fun(A,B) ×c A → B such that for all X, the comparison
-- Map(X, Fun(A,B)) → Map(X ×c A, B) is an equivalence.
------------------------------------------------------------------------

postulate
  Fun : Cat → Cat → Cat
  ev  : (A B : Cat) → Map (Fun A B ×c A) B

exp-comparison : (A B X : Cat) → Map X (Fun A B) → Map (X ×c A) B
exp-comparison A B X u =
  comp (ev A B) ⟨ comp u (π₁ X A) , π₂ X A ⟩

postulate
  exp-is-equiv : (A B X : Cat) → is-equiv (exp-comparison A B X)

exp-equiv : (A B X : Cat) → Map X (Fun A B) ≃ Map (X ×c A) B
exp-equiv A B X = exp-comparison A B X , exp-is-equiv A B X

------------------------------------------------------------------------
-- Remark 16 (part): Ob(Fun(A,B)) ≃ Map(A,B)
--
-- The exponential equivalence at X = 𝟏c gives
--   Ob(Fun(A,B)) ≃ Map(𝟏c ×c A, B).
-- Since 𝟏c ×c A ≅ A (the terminal category is a unit for products),
-- we get Ob(Fun(A,B)) ≃ Map(A,B).
------------------------------------------------------------------------

-- The canonical map A → 𝟏c ×c A (pairing the unique map with id)

unit-right : (A : Cat) → Map A (𝟏c ×c A)
unit-right A = ⟨ ! A , idMap A ⟩

-- Forward: Ob(Fun(A,B)) → Map(A,B)

ob-to-map : (A B : Cat) → Ob (Fun A B) → Map A B
ob-to-map A B f = comp (exp-comparison A B 𝟏c f) (unit-right A)

-- Backward: Map(A,B) → Ob(Fun(A,B))

map-to-ob : (A B : Cat) → Map A B → Ob (Fun A B)
map-to-ob A B g = equiv-inv (exp-equiv A B 𝟏c) (comp g (π₂ 𝟏c A))

-- Round-trip 1: ob-to-map (map-to-ob g) ≡ g

ob-map-roundtrip₁ : (A B : Cat) (g : Map A B)
                   → ob-to-map A B (map-to-ob A B g) ≡ g
ob-map-roundtrip₁ A B g =
  ap (λ h → comp h (unit-right A))
     (equiv-inv-rinv (exp-equiv A B 𝟏c) (comp g (π₂ 𝟏c A)))
  ∙ (comp-assoc g (π₂ 𝟏c A) (unit-right A)) ⁻¹
  ∙ ap (comp g) (pair-β₂ (! A) (idMap A))
  ∙ comp-id-r g

------------------------------------------------------------------------
-- Key lemma: unit-right is a section of π₂ (left unit law)
--
-- comp (unit-right A) (π₂ 𝟏c A) ≡ idMap (𝟏c ×c A)
--
-- Proof by injectivity of pb-comparison (which is an equivalence).
-- We build the cone equality using a helper that pattern-matches on
-- the component paths, avoiding transport headaches.
------------------------------------------------------------------------

-- Helper: two cones over 𝟏c are equal when their Map-components match
-- (the path component is automatic since Map(X,𝟏c) is a set).

cone-eq-𝟏c : (A X : Cat)
            → {h₁ h₂ : Map X 𝟏c} {k₁ k₂ : Map X A}
            → {p₁ : comp (! 𝟏c) h₁ ≡ comp (! A) k₁}
            → {p₂ : comp (! 𝟏c) h₂ ≡ comp (! A) k₂}
            → h₁ ≡ h₂ → k₁ ≡ k₂
            → (h₁ , k₁ , p₁) ≡ (h₂ , k₂ , p₂)
cone-eq-𝟏c A X (refl _) (refl _) =
  to-Σ-≡ (refl _ , to-Σ-≡ (refl _ ,
    props-are-sets (singletons-are-props (terminal X)) _ _ _ _))

unit-left : (A : Cat)
           → comp (unit-right A) (π₂ 𝟏c A) ≡ idMap (𝟏c ×c A)
unit-left A = equiv-inj
  (pb-comparison (! 𝟏c) (! A) P)
  (pb-is-equiv (! 𝟏c) (! A) P)
  (cone-eq-𝟏c A P eq₁ eq₂)
  where
    P = 𝟏c ×c A
    u = comp (unit-right A) (π₂ 𝟏c A)

    -- First components: both in Map P 𝟏c, which is contractible
    eq₁ : comp (π₁ 𝟏c A) u ≡ comp (π₁ 𝟏c A) (idMap P)
    eq₁ = singletons-are-props (terminal P) _ _

    -- Second components: both reduce to π₂
    eq₂ : comp (π₂ 𝟏c A) u ≡ comp (π₂ 𝟏c A) (idMap P)
    eq₂ = comp-assoc (π₂ 𝟏c A) (unit-right A) (π₂ 𝟏c A)
        ∙ ap (λ m → comp m (π₂ 𝟏c A)) (pair-β₂ (! A) (idMap A))
        ∙ comp-id-l (π₂ 𝟏c A)
        ∙ (comp-id-r (π₂ 𝟏c A)) ⁻¹

------------------------------------------------------------------------
-- Round-trip 2: map-to-ob (ob-to-map f) ≡ f
--
-- map-to-ob (ob-to-map f)
--   = equiv-inv e (comp (comp (exp-comp f) (unit-right A)) π₂)
--   = equiv-inv e (comp (exp-comp f) (comp (unit-right A) π₂))  [assoc⁻¹]
--   = equiv-inv e (comp (exp-comp f) id)                        [unit-left]
--   = equiv-inv e (exp-comp f)                                  [comp-id-r]
--   = f                                                         [equiv-inv-linv]
------------------------------------------------------------------------

ob-map-roundtrip₂ : (A B : Cat) (f : Ob (Fun A B))
                   → map-to-ob A B (ob-to-map A B f) ≡ f
ob-map-roundtrip₂ A B f =
  ap (equiv-inv e)
     ((comp-assoc (exp-comparison A B 𝟏c f) (unit-right A) (π₂ 𝟏c A)) ⁻¹
      ∙ ap (comp (exp-comparison A B 𝟏c f)) (unit-left A)
      ∙ comp-id-r (exp-comparison A B 𝟏c f))
  ∙ equiv-inv-linv e f
  where
    e = exp-equiv A B 𝟏c
