{-# OPTIONS --without-K --exact-split #-}

module Squares.PushoutDef where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Interval.OrdCompare
open import Simplices.LastEdge
open import Interval.FaceOrd
open import Simplices.FaceMap
open import Simplices.FaceTop
open import Category.ExpEval
open import Simplices.FaceTopProof

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
