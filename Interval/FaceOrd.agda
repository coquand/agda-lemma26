{-# OPTIONS --without-K --exact-split #-}

module Interval.FaceOrd where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Interval.OrdCompare

face-ord : (n : ℕ) → Ord n → Ord n → 𝟚
face-ord n v u = pr₁ (monotone-ord-bwd n (inl v)) u

face-ord-mono-u : (n : ℕ) (v : Ord n) (u u' : Ord n)
  → u ≤Ord u' → face-ord n v u ≤𝟚 face-ord n v u'
face-ord-mono-u n v u u' le = pr₂ (monotone-ord-bwd n (inl v)) u u' le

face-ord-mono-v : (n : ℕ) (v v' : Ord n) (u : Ord n)
  → v ≤Ord v' → face-ord n v u ≤𝟚 face-ord n v' u
face-ord-mono-v n v v' u le = monotone-ord-bwd-pw n (inl v) (inl v') le u

face-ord-mono : (n : ℕ) (v v' u u' : Ord n)
  → v ≤Ord v' → u ≤Ord u'
  → face-ord n v u ≤𝟚 face-ord n v' u'
face-ord-mono n v v' u u' lev leu =
  ≤𝟚-trans (face-ord-mono-v n v v' u lev) (face-ord-mono-u n v' u u' leu)
