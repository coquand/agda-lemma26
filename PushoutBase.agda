{-# OPTIONS --without-K --exact-split #-}

module PushoutBase where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import Segal
open import OrdCompare
open import LastEdge
open import FaceOrd
open import FaceMap
open import FaceTop
open import ExpEval
open import FaceTopProof
open import UnitIso
open import SigmaEquiv

eval-pt-ob : (f : Ob (Δ (suc zero))) → comp eval-pt f ≡ ob-to-map 𝟏c 𝕀 f
eval-pt-ob f =
  eval-pt-eq 𝟏c f
  ∙ ap (comp (exp-comparison 𝟏c 𝕀 𝟏c f))
      (pair-ap (singletons-are-props (terminal 𝟏c) (idMap 𝟏c) (! 𝟏c))
               (singletons-are-props (terminal 𝟏c) (! 𝟏c) (idMap 𝟏c)))

eval-pt-dom-last : comp eval-pt (dom (last-edge zero)) ≡ 𝕀₀
eval-pt-dom-last = equiv-inj (pr₁ 𝕀-ob) (pr₂ 𝕀-ob)
  (ap (pr₁ 𝕀-ob) (eval-pt-ob (dom (last-edge zero)))
   ∙ ap (λ x → pr₁ 𝕀-ob (ob-to-map 𝟏c 𝕀 x)) ((face-top zero) ⁻¹)
   ∙ ap (pr₁ 𝕀-ob) ((comp-id-r (ob-to-map 𝟏c 𝕀 (comp (face zero) (top zero)))) ⁻¹)
   ∙ face-pw zero (idMap 𝟏c)
   ∙ (equiv-inv-rinv 𝕀-ob (inl ⋆)) ⁻¹)

eval-pt-top1 : comp eval-pt (top (suc zero)) ≡ 𝕀₁
eval-pt-top1 =
  eval-pt-ob (top (suc zero))
  ∙ ob-map-roundtrip₁ 𝟏c 𝕀 (comp 𝕀₁ (! 𝟏c))
  ∙ ap (comp 𝕀₁) (singletons-are-props (terminal 𝟏c) (! 𝟏c) (idMap 𝟏c))
  ∙ comp-id-r 𝕀₁

eval-pt-last-edge : comp eval-pt (last-edge zero) ≡ idMap 𝕀
eval-pt-last-edge = ap pr₁ (singletons-are-props 𝕀-hom-contr h₁ h₂)
  where
    h₁ : Hom 𝕀 𝕀₀ 𝕀₁
    h₁ = comp eval-pt (last-edge zero) ,
      dom-nat eval-pt (last-edge zero) ∙ eval-pt-dom-last ,
      cod-nat eval-pt (last-edge zero) ∙ ap (comp eval-pt) (edge-cod zero) ∙ eval-pt-top1
    h₂ : Hom 𝕀 𝕀₀ 𝕀₁
    h₂ = idMap 𝕀 , comp-id-l 𝕀₀ , comp-id-l 𝕀₁
