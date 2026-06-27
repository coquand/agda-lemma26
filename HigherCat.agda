{-# OPTIONS --without-K --exact-split #-}

module HigherCat where

open import Spartan
open import CatAxioms

------------------------------------------------------------------------
-- Lemma: A map between contractible types is an equivalence
------------------------------------------------------------------------

map-between-contrs-is-equiv : {A : Type 𝓤} {B : Type 𝓥}
  → (f : A → B) → is-contr A → is-contr B → is-equiv f
map-between-contrs-is-equiv f (a₀ , φ) (b₀ , ψ) y = (a₀ , q) , γ
  where
    q : f a₀ ≡ y
    q = singletons-are-props (b₀ , ψ) (f a₀) y
    γ : (w : fiber f y) → (a₀ , q) ≡ w
    γ (x , p) = to-Σ-≡ (φ x ,
      props-are-sets (singletons-are-props (b₀ , ψ)) (f x) y
        (transport (λ z → f z ≡ y) (φ x) q) p)

------------------------------------------------------------------------
-- Terminal categories
------------------------------------------------------------------------

is-terminal : Cat → Type (𝓤₀ ⁺)
is-terminal T = (C : Cat) → is-contr (Map C T)

is-terminal-is-prop : (T : Cat) → is-prop (is-terminal T)
is-terminal-is-prop T = Π-is-prop (λ C → being-contr-is-prop)

------------------------------------------------------------------------
-- Any functor between terminal categories is an iso
--
-- If T₁ and T₂ are terminal, then for any X, both Map(X,T₁) and
-- Map(X,T₂) are contractible. So post-composition with any
-- f : Map T₁ T₂ is a map between contractible types, hence an equiv.
------------------------------------------------------------------------

terminal-map-isIso : {T₁ T₂ : Cat}
  → is-terminal T₁ → is-terminal T₂
  → (f : Map T₁ T₂) → isIso f
terminal-map-isIso h₁ h₂ f X =
  map-between-contrs-is-equiv (post-comp f X) (h₁ X) (h₂ X)

------------------------------------------------------------------------
-- Remark 5: There is only one terminal category
--
-- Proof: Given two terminal categories (T₁,h₁) and (T₂,h₂),
-- pick any f : Map T₁ T₂ (exists since Map T₁ T₂ is contractible).
-- Then f is an iso (by the above), giving elements
--   e₁ = (T₁, g, _) and e₂ = (T₂, f, _)  in  Equiv-from T₁.
-- Since Equiv-from T₁ is contractible (cat-univalence), e₁ ≡ e₂.
-- Project to get T₁ ≡ T₂; the second component follows since
-- is-terminal is a proposition.
------------------------------------------------------------------------

terminal-is-prop : is-prop (Σ T ꞉ Cat , is-terminal T)
terminal-is-prop (T₁ , h₁) (T₂ , h₂) = to-Σ-≡ (p , q)
  where
    e₁ : Equiv-from T₁
    e₁ = T₁ , center (h₁ T₁) , terminal-map-isIso h₁ h₁ (center (h₁ T₁))
    e₂ : Equiv-from T₁
    e₂ = T₂ , center (h₂ T₁) , terminal-map-isIso h₁ h₂ (center (h₂ T₁))
    p : T₁ ≡ T₂
    p = ap pr₁ (singletons-are-props (cat-univalence T₁) e₁ e₂)
    q : transport is-terminal p h₁ ≡ h₂
    q = is-terminal-is-prop T₂ (transport is-terminal p h₁) h₂

------------------------------------------------------------------------
-- The two-element type
------------------------------------------------------------------------

𝟚 : Type 𝓤₀
𝟚 = 𝟙 + 𝟙

------------------------------------------------------------------------
-- Axiom 8: The walking arrow
--
-- We postulate a category 𝕀 together with an equivalence
-- Ob(𝕀) ≃ 𝟚 between its objects and the two-element type.
------------------------------------------------------------------------

postulate
  𝕀    : Cat
  𝕀-ob : Ob 𝕀 ≃ 𝟚

------------------------------------------------------------------------
-- Definition 10: Morphisms in a category
--
-- A morphism in C is a functor 𝕀 → C.
------------------------------------------------------------------------

Mor : Cat → Type 𝓤₀
Mor C = Map 𝕀 C

------------------------------------------------------------------------
-- Injectivity of equivalences
------------------------------------------------------------------------

equiv-inj : {A : Type 𝓤} {B : Type 𝓥} (f : A → B)
          → is-equiv f → {x y : A} → f x ≡ f y → x ≡ y
equiv-inj f ef {x} {y} p =
  ap pr₁ (singletons-are-props (ef (f x)) (x , refl (f x)) (y , p ⁻¹))

------------------------------------------------------------------------
-- Remark: An isomorphism has a two-sided inverse
--
-- If f : Map C D is an iso, then f has an inverse g : Map D C with
--   comp f g ≡ idMap D   and   comp g f ≡ idMap C.
--
-- Right inverse: post-comp f D is an equivalence, so the fiber over
-- idMap D is contractible. Its center gives g with comp f g ≡ idMap D.
--
-- Left inverse: we have
--   comp f (comp g f) ≡ comp (comp f g) f ≡ comp (idMap D) f ≡ f
-- and
--   comp f (idMap C) ≡ f.
-- Since post-comp f C is an equivalence (hence injective),
-- comp g f ≡ idMap C.
------------------------------------------------------------------------

isIso-inverse : {C D : Cat} (f : Map C D) → isIso f
              → Σ g ꞉ Map D C , (comp f g ≡ idMap D) × (comp g f ≡ idMap C)
isIso-inverse {C} {D} f iso = g , rinv , linv
  where
    g : Map D C
    g = pr₁ (center (iso D (idMap D)))
    rinv : comp f g ≡ idMap D
    rinv = pr₂ (center (iso D (idMap D)))
    linv : comp g f ≡ idMap C
    linv = equiv-inj (post-comp f C) (iso C)
             (comp-assoc f g f
              ∙ ap (λ m → comp m f) rinv
              ∙ comp-id-l f
              ∙ (comp-id-r f) ⁻¹)
