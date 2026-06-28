{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- 𝕀-specific geometry for the posetal development (the geometric layer, Lemma 26).
--
-- These are the facts about the walking arrow 𝕀 that feed `I-posetal`
-- (Posetal.agda) but do NOT mention the posetal predicate / object-action
-- (so this module sits strictly below Posetal and avoids a cycle):
--   * `val-𝕀`        : every object of 𝕀 is 𝕀₀ or 𝕀₁  (Rocq `values_𝕀`)
--   * `map-into-𝕀-eq`: maps into 𝕀 agree iff they agree on objects
--   * `𝕀-thin`       : Hom 𝕀 is a proposition  (Rocq `isaprop_𝕀_edge`)
--   * `𝕀-hom-to-order`: a morphism in 𝕀 orders its endpoints under 𝕀-ob
------------------------------------------------------------------------

module Interval.IntervalPosetal where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat using (𝕀; 𝕀-ob; 𝟚; Mor; equiv-inj)
open import Category.Constructions using (𝕀₀; 𝕀₁; dom; cod; Hom; equiv-inv; id-hom)
open import Category.Pullbacks using (equiv-inv-rinv; equiv-inv-linv)
open import Interval.Interval
  using (ob-to-𝟚; 𝕀-char; 𝕀-char-comparison; 𝕀-char-inverse;
         𝕀-char-rinv; 𝕀-char-linv; _≤𝟚_; ≤𝟚-transport; is-monotone;
         is-monotone-is-prop; 𝕀-mor-order; Hom-coerce)
open import Foundations.HLevels using (ob-𝕀-is-set; ×-is-prop)

------------------------------------------------------------------------
-- Every object of 𝕀 is 𝕀₀ or 𝕀₁
------------------------------------------------------------------------

val-𝕀-aux : (z : Ob 𝕀) (b : 𝟚) → pr₁ 𝕀-ob z ≡ b → (z ≡ 𝕀₀) + (z ≡ 𝕀₁)
val-𝕀-aux z (inl ⋆) eq = inl ((equiv-inv-linv 𝕀-ob z) ⁻¹ ∙ ap (equiv-inv 𝕀-ob) eq)
val-𝕀-aux z (inr ⋆) eq = inr ((equiv-inv-linv 𝕀-ob z) ⁻¹ ∙ ap (equiv-inv 𝕀-ob) eq)

val-𝕀 : (z : Ob 𝕀) → (z ≡ 𝕀₀) + (z ≡ 𝕀₁)
val-𝕀 z = val-𝕀-aux z (pr₁ 𝕀-ob z) (refl (pr₁ 𝕀-ob z))

------------------------------------------------------------------------
-- Values of 𝕀-ob on the two objects
------------------------------------------------------------------------

𝕀-ob-𝕀₀ : pr₁ 𝕀-ob 𝕀₀ ≡ inl ⋆
𝕀-ob-𝕀₀ = equiv-inv-rinv 𝕀-ob (inl ⋆)

𝕀-ob-𝕀₁ : pr₁ 𝕀-ob 𝕀₁ ≡ inr ⋆
𝕀-ob-𝕀₁ = equiv-inv-rinv 𝕀-ob (inr ⋆)

------------------------------------------------------------------------
-- Maps into 𝕀 are determined by their action on objects
-- (the engine of `posetal-eq-objects`, proved here directly from 𝕀-char
--  so that 𝕀-thin does not depend on posetality).
------------------------------------------------------------------------

map-into-𝕀-eq : {A : Cat} (m1 m2 : Map A 𝕀)
  → ((z : Ob A) → comp m1 z ≡ comp m2 z) → m1 ≡ m2
map-into-𝕀-eq {A} m1 m2 e =
  equiv-inj (𝕀-char-comparison A) (pr₂ (𝕀-char A))
    (to-Σ-≡ (funext (λ z → ap (pr₁ 𝕀-ob) (e z)) ,
             is-monotone-is-prop (ob-to-𝟚 m2) _ _))

------------------------------------------------------------------------
-- A morphism in 𝕀 orders its endpoints (under the 𝕀-ob enumeration)
------------------------------------------------------------------------

𝕀-hom-to-order : (a b : Ob 𝕀) → Hom 𝕀 a b → pr₁ 𝕀-ob a ≤𝟚 pr₁ 𝕀-ob b
𝕀-hom-to-order a b (m , dm , cm) =
  ≤𝟚-transport (ap (pr₁ 𝕀-ob) dm) (ap (pr₁ 𝕀-ob) cm) (𝕀-mor-order m)

------------------------------------------------------------------------
-- Hom 𝕀 is thin  (Rocq `isaprop_𝕀_edge`, Main.v 4006)
------------------------------------------------------------------------

𝕀-thin : (x y : Ob 𝕀) → is-prop (Hom 𝕀 x y)
𝕀-thin x y (m1 , d1 , c1) (m2 , d2 , c2) =
  to-Σ-≡ (m1≡m2 ,
          ×-is-prop (ob-𝕀-is-set (dom m2) x) (ob-𝕀-is-set (cod m2) y)
            _ (d2 , c2))
  where
    agree : (z : Ob 𝕀) → comp m1 z ≡ comp m2 z
    agree z = +-induction (λ _ → comp m1 z ≡ comp m2 z)
      (λ e0 → ap (comp m1) e0 ∙ d1 ∙ d2 ⁻¹ ∙ ap (comp m2) (e0 ⁻¹))
      (λ e1 → ap (comp m1) e1 ∙ c1 ∙ c2 ⁻¹ ∙ ap (comp m2) (e1 ⁻¹))
      (val-𝕀 z)
    m1≡m2 : m1 ≡ m2
    m1≡m2 = map-into-𝕀-eq m1 m2 agree

------------------------------------------------------------------------
-- Building a morphism in 𝕀 from an order relation (converse of
-- 𝕀-hom-to-order).  The generating edge plus the two identities cover
-- the three monotone cases; the descending case is absurd.
------------------------------------------------------------------------

gen-hom : Hom 𝕀 𝕀₀ 𝕀₁
gen-hom = idMap 𝕀 , comp-id-l 𝕀₀ , comp-id-l 𝕀₁

𝕀-order-to-hom : (a b : Ob 𝕀) → pr₁ 𝕀-ob a ≤𝟚 pr₁ 𝕀-ob b → Hom 𝕀 a b
𝕀-order-to-hom a b le =
  +-induction (λ _ → Hom 𝕀 a b)
    (λ ea0 → +-induction (λ _ → Hom 𝕀 a b)
       (λ eb0 → Hom-coerce (ea0 ⁻¹) (eb0 ⁻¹) (id-hom 𝕀₀))
       (λ eb1 → Hom-coerce (ea0 ⁻¹) (eb1 ⁻¹) gen-hom)
       (val-𝕀 b))
    (λ ea1 → +-induction (λ _ → Hom 𝕀 a b)
       (λ eb0 → 𝟘-elim (≤𝟚-transport (ap (pr₁ 𝕀-ob) ea1 ∙ 𝕀-ob-𝕀₁)
                                     (ap (pr₁ 𝕀-ob) eb0 ∙ 𝕀-ob-𝕀₀) le))
       (λ eb1 → Hom-coerce (ea1 ⁻¹) (eb1 ⁻¹) (id-hom 𝕀₁))
       (val-𝕀 b))
    (val-𝕀 a)
