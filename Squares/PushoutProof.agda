{-# OPTIONS --without-K --exact-split #-}

module Squares.PushoutProof where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Simplices.Segal
open import Interval.OrdCompare
open import Simplices.LastEdge
open import Interval.FaceOrd
open import Simplices.FaceMap
open import Simplices.FaceTop
open import Category.ExpEval
open import Simplices.FaceTopProof
open import Category.UnitIso
open import Squares.PushoutBase
open import Foundations.SigmaEquiv
open import Squares.PushoutDef

eval-pt-data : Σ g ꞉ Map 𝕀 (Δ (suc zero)) , (comp eval-pt g ≡ idMap 𝕀) × (comp g eval-pt ≡ idMap (Δ (suc zero)))
eval-pt-data = isIso-inverse eval-pt eval-pt-isIso

-- kept `opaque`: `eval-pt-inv` unfolds to a heavy `isIso-inverse`, and
-- normalizing it during downstream implicit-argument inference cost ~37 s
-- (in SegalGeom).  Its three components must share one opaque block so the
-- round-trip types still see `eval-pt-inv = pr₁ eval-pt-data`.
opaque
  eval-pt-inv : Map 𝕀 (Δ (suc zero))
  eval-pt-inv = pr₁ eval-pt-data

  eval-pt-rinv : comp eval-pt eval-pt-inv ≡ idMap 𝕀
  eval-pt-rinv = pr₁ (pr₂ eval-pt-data)

  eval-pt-linv : comp eval-pt-inv eval-pt ≡ idMap (Δ (suc zero))
  eval-pt-linv = pr₂ (pr₂ eval-pt-data)

eval-pt-inv-eq : eval-pt-inv ≡ last-edge zero
eval-pt-inv-eq = equiv-inj (post-comp eval-pt 𝕀) (eval-pt-isIso 𝕀)
  (eval-pt-rinv ∙ eval-pt-last-edge ⁻¹)

last-edge-0-linv : comp (last-edge zero) eval-pt ≡ idMap (Δ (suc zero))
last-edge-0-linv = ap (λ g → comp g eval-pt) (eval-pt-inv-eq ⁻¹) ∙ eval-pt-linv

face-0-is-dom : face zero ≡ dom (last-edge zero)
face-0-is-dom =
  (comp-id-r (face zero)) ⁻¹
  ∙ ap (comp (face zero)) (singletons-are-props (terminal 𝟏c) (idMap 𝟏c) (top zero))
  ∙ face-top zero

pushout-inv-0 : (C : Cat) → PushoutPair zero C → Map (Δ (suc zero)) C
pushout-inv-0 C (σ , m , p) = comp m eval-pt

pushout-linv-0 : (C : Cat) (α : Map (Δ (suc zero)) C)
  → pushout-inv-0 C (pushout-comparison zero C α) ≡ α
pushout-linv-0 C α =
  (comp-assoc α (last-edge zero) eval-pt) ⁻¹
  ∙ ap (comp α) last-edge-0-linv
  ∙ comp-id-r α

pushout-σ-eq : (C : Cat) (σ : Ob C) (m : Mor C) (p : comp σ (top zero) ≡ dom m)
  → comp (comp m eval-pt) (face zero) ≡ σ
pushout-σ-eq C σ m p =
  (comp-assoc m eval-pt (face zero)) ⁻¹
  ∙ ap (comp m) (ap (comp eval-pt) face-0-is-dom ∙ eval-pt-dom-last)
  ∙ p ⁻¹
  ∙ ap (comp σ) (singletons-are-props (terminal 𝟏c) (top zero) (idMap 𝟏c))
  ∙ comp-id-r σ

pushout-m-eq : (C : Cat) (m : Mor C)
  → comp (comp m eval-pt) (last-edge zero) ≡ m
pushout-m-eq C m =
  (comp-assoc m eval-pt (last-edge zero)) ⁻¹
  ∙ ap (comp m) eval-pt-last-edge
  ∙ comp-id-r m

comp-top-is-equiv : (C : Cat) → is-equiv (λ (σ : Ob C) → comp σ (top zero))
comp-top-is-equiv C = transport is-equiv
  (funext (λ σ → (ap (comp σ) (singletons-are-props (terminal 𝟏c) (top zero) (idMap 𝟏c))
                   ∙ comp-id-r σ) ⁻¹))
  (id-is-equiv (Ob C))

pushout-rinv-0 : (C : Cat) (t : PushoutPair zero C)
  → pushout-comparison zero C (pushout-inv-0 C t) ≡ t
pushout-rinv-0 C (σ , m , p) = ap unswap swapped-path
  where
    α : Map (Δ (suc zero)) C
    α = comp m eval-pt
    lhs : PushoutPair zero C
    lhs = pushout-comparison zero C α
    F : Mor C → Type 𝓤₀
    F m' = Σ σ' ꞉ Ob C , comp σ' (top zero) ≡ dom m'
    unswap : (Σ m' ꞉ Mor C , F m') → PushoutPair zero C
    unswap (m' , σ' , p') = (σ' , m' , p')
    swapped-path : (pr₁ (pr₂ lhs) , pr₁ lhs , pr₂ (pr₂ lhs)) ≡ (m , σ , p)
    swapped-path = to-Σ-≡ (pushout-m-eq C m ,
      singletons-are-props (comp-top-is-equiv C (dom m))
        (transport F (pushout-m-eq C m) (pr₁ lhs , pr₂ (pr₂ lhs)))
        (σ , p))

pushout-is-equiv-0 : (C : Cat) → is-equiv (pushout-comparison zero C)
pushout-is-equiv-0 C = invertible-to-equiv (pushout-comparison zero C)
  (pushout-inv-0 C , pushout-rinv-0 C , pushout-linv-0 C)
