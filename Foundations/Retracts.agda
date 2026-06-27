{-# OPTIONS --without-K --exact-split #-}

module Foundations.Retracts where

open import Foundations.Spartan
open import Category.CatAxioms
open import Interval.Interval

------------------------------------------------------------------------
-- A functor with a two-sided inverse is an isomorphism
--
-- Given f : Map C D with inverse g, post-composition with f is
-- invertible (via post-composition with g), hence an equivalence.
------------------------------------------------------------------------

has-inverse-isIso : {C D : Cat} (f : Map C D)
  (g : Map D C) → comp f g ≡ idMap D → comp g f ≡ idMap C
  → isIso f
has-inverse-isIso {C} {D} f g fg gf X =
  invertible-to-equiv (post-comp f X)
    (post-comp g X ,
     (λ h → comp-assoc f g h ∙ ap (λ m → comp m h) fg ∙ comp-id-l h) ,
     (λ h' → comp-assoc g f h' ∙ ap (λ m → comp m h') gf ∙ comp-id-l h'))

------------------------------------------------------------------------
-- Lemma 25: Isomorphisms are closed under retracts [0018]
--
-- Let A, B₀, B₁ : Cat.  Suppose sᵢ : Bᵢ → A and rᵢ : A → Bᵢ
-- satisfy rᵢ ∘ sᵢ = id (i = 0, 1).  If f : B₀ → B₁ satisfies
-- s₁ ∘ f = s₀  and  f ∘ r₀ = r₁,  then f is an isomorphism
-- with explicit inverse  g = r₀ ∘ s₁.
--
-- Proof:
--   f ∘ g = f ∘ (r₀ ∘ s₁) = (f ∘ r₀) ∘ s₁ = r₁ ∘ s₁ = id
--   g ∘ f = (r₀ ∘ s₁) ∘ f = r₀ ∘ (s₁ ∘ f) = r₀ ∘ s₀ = id
------------------------------------------------------------------------

retract-inverse : {A B₀ B₁ : Cat}
  (s₀ : Map B₀ A) (r₀ : Map A B₀) (r₀s₀ : comp r₀ s₀ ≡ idMap B₀)
  (s₁ : Map B₁ A) (r₁ : Map A B₁) (r₁s₁ : comp r₁ s₁ ≡ idMap B₁)
  (f : Map B₀ B₁) (sf : comp s₁ f ≡ s₀) (fr : comp f r₀ ≡ r₁)
  → Σ g ꞉ Map B₁ B₀ , (comp f g ≡ idMap B₁) × (comp g f ≡ idMap B₀)
retract-inverse s₀ r₀ r₀s₀ s₁ r₁ r₁s₁ f sf fr =
  g , fg , gf
  where
    g = comp r₀ s₁
    fg = comp-assoc f r₀ s₁ ∙ ap (λ m → comp m s₁) fr ∙ r₁s₁
    gf = (comp-assoc r₀ s₁ f) ⁻¹ ∙ ap (comp r₀) sf ∙ r₀s₀

retract-iso : {A B₀ B₁ : Cat}
  (s₀ : Map B₀ A) (r₀ : Map A B₀) (r₀s₀ : comp r₀ s₀ ≡ idMap B₀)
  (s₁ : Map B₁ A) (r₁ : Map A B₁) (r₁s₁ : comp r₁ s₁ ≡ idMap B₁)
  (f : Map B₀ B₁) (sf : comp s₁ f ≡ s₀) (fr : comp f r₀ ≡ r₁)
  → isIso f
retract-iso s₀ r₀ r₀s₀ s₁ r₁ r₁s₁ f sf fr =
  has-inverse-isIso f g fg gf
  where
    inv = retract-inverse s₀ r₀ r₀s₀ s₁ r₁ r₁s₁ f sf fr
    g  = pr₁ inv
    fg = pr₁ (pr₂ inv)
    gf = pr₂ (pr₂ inv)
