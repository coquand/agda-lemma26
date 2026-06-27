{-# OPTIONS --without-K --exact-split #-}

module Category.UnitIso where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Foundations.Retracts

right-unit-cat : (X : Cat) → Map X (X ×c 𝟏c)
right-unit-cat X = ⟨ idMap X , ! X ⟩

eval-pt : Map (Fun 𝟏c 𝕀) 𝕀
eval-pt = comp (ev 𝟏c 𝕀) (right-unit-cat (Fun 𝟏c 𝕀))

right-unit-retract : (X : Cat)
  → comp (π₁ X 𝟏c) (right-unit-cat X) ≡ idMap X
right-unit-retract X = pair-β₁ (idMap X) (! X)

right-unit-section : (X : Cat)
  → comp (right-unit-cat X) (π₁ X 𝟏c) ≡ idMap (X ×c 𝟏c)
right-unit-section X =
  pair-nat (idMap X) (! X) (π₁ X 𝟏c)
  ∙ pair-ap (comp-id-l (π₁ X 𝟏c))
            (singletons-are-props (terminal (X ×c 𝟏c))
              (comp (! X) (π₁ X 𝟏c)) (π₂ X 𝟏c))
  ∙ pair-ap ((comp-id-r (π₁ X 𝟏c)) ⁻¹) ((comp-id-r (π₂ X 𝟏c)) ⁻¹)
  ∙ pair-η (idMap (X ×c 𝟏c))

right-unit-isIso : (X : Cat) → isIso (right-unit-cat X)
right-unit-isIso X = has-inverse-isIso (right-unit-cat X) (π₁ X 𝟏c)
  (right-unit-section X) (right-unit-retract X)

eval-pt-eq : (Y : Cat) (u : Map Y (Fun 𝟏c 𝕀))
  → comp eval-pt u
    ≡ comp (exp-comparison 𝟏c 𝕀 Y u) (right-unit-cat Y)
eval-pt-eq Y u = lhs ∙ rhs ⁻¹
  where
    F = Fun 𝟏c 𝕀
    lhs : comp eval-pt u ≡ comp (ev 𝟏c 𝕀) ⟨ u , ! Y ⟩
    lhs =
      (comp-assoc (ev 𝟏c 𝕀) (right-unit-cat F) u) ⁻¹
      ∙ ap (comp (ev 𝟏c 𝕀))
          (pair-nat (idMap F) (! F) u
           ∙ pair-ap (comp-id-l u)
               (singletons-are-props (terminal Y)
                 (comp (! F) u) (! Y)))
    rhs : comp (exp-comparison 𝟏c 𝕀 Y u) (right-unit-cat Y)
        ≡ comp (ev 𝟏c 𝕀) ⟨ u , ! Y ⟩
    rhs =
      (comp-assoc (ev 𝟏c 𝕀)
        ⟨ comp u (π₁ Y 𝟏c) , π₂ Y 𝟏c ⟩ (right-unit-cat Y)) ⁻¹
      ∙ ap (comp (ev 𝟏c 𝕀))
          (pair-nat (comp u (π₁ Y 𝟏c)) (π₂ Y 𝟏c) (right-unit-cat Y)
           ∙ pair-ap
               ((comp-assoc u (π₁ Y 𝟏c) (right-unit-cat Y)) ⁻¹
                ∙ ap (comp u) (pair-β₁ (idMap Y) (! Y))
                ∙ comp-id-r u)
               (pair-β₂ (idMap Y) (! Y)))

pre-comp-right-unit : (Y : Cat)
  → Map (Y ×c 𝟏c) 𝕀 ≃ Map Y 𝕀
pre-comp-right-unit Y =
  (λ h → comp h (right-unit-cat Y)) ,
  invertible-to-equiv (λ h → comp h (right-unit-cat Y))
    ((λ h' → comp h' (π₁ Y 𝟏c)) ,
     (λ h' → (comp-assoc h' (π₁ Y 𝟏c) (right-unit-cat Y)) ⁻¹
              ∙ ap (comp h') (right-unit-retract Y)
              ∙ comp-id-r h') ,
     (λ h → (comp-assoc h (right-unit-cat Y) (π₁ Y 𝟏c)) ⁻¹
            ∙ ap (comp h) (right-unit-section Y)
            ∙ comp-id-r h))

eval-pt-isIso : isIso eval-pt
eval-pt-isIso Y =
  transport is-equiv ((funext (eval-pt-eq Y)) ⁻¹)
    (pr₂ (equiv-comp (exp-equiv 𝟏c 𝕀 Y) (pre-comp-right-unit Y)))
