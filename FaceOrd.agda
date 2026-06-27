{-# OPTIONS --without-K --exact-split #-}

module FaceOrd where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import OrdCompare

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
