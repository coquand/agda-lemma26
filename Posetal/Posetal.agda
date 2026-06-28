{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — SHARED interface (the geometric layer ⇄ the pushout-algebra layer contract).
--
-- the geometric layer's four deliverables, all PROVED (postulate-free):
--   posetal-eq-objects, posetal-hom-is-set, I-posetal   (PosetalCore)
--   Delta-posetal                                        (here, by induction:
--       base Δ0 = 𝟏c is posetal; step Δ(suc n) = Fun (Δ n) 𝕀 via Fun-I-posetal)
--
-- `is-posetal` carries a third clause `is-set (Ob C)`, matching Rocq's
-- separate `isaset (Ob C)` hypothesis (Main.v 3930).  The heavy curry/uncurry
-- construction for `Fun X 𝕀` lives in `FunIPosetal` (behind a module boundary
-- so each file type-checks within budget); this module just re-exports and
-- assembles the induction.
------------------------------------------------------------------------

module Posetal.Posetal where

open import Foundations.Spartan
open import Category.CatAxioms using (Cat)
open import Interval.Interval using (Δ)
open import Posetal.PosetalCore public
open import Posetal.FunIPosetal public

Delta-posetal : (n : ℕ) → is-posetal (Δ n)
Delta-posetal zero    = is-posetal-𝟏c
Delta-posetal (suc n) = Fun-I-posetal (Δ n)
