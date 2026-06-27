{-# OPTIONS --without-K --exact-split #-}

module PushoutDef where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import OrdCompare
open import LastEdge
open import FaceOrd
open import FaceMap
open import FaceTop
open import ExpEval
open import FaceTopProof

PushoutPair : ℕ → Cat → Type 𝓤₀
PushoutPair n C =
  Σ σ ꞉ Map (Δ n) C , Σ m ꞉ Mor C , Ob-map σ (top n) ≡ dom m

pushout-comparison : (n : ℕ) (C : Cat)
                   → Map (Δ (suc n)) C → PushoutPair n C
pushout-comparison n C α =
  comp α (face n) ,
  comp α (last-edge n) ,
  (comp-assoc α (face n) (top n)) ⁻¹
  ∙ ap (comp α) (face-top n)
  ∙ comp-assoc α (last-edge n) 𝕀₀
