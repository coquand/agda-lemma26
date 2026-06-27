{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — SHARED interface (Stream A ⇄ Stream B contract).
--
-- The abstract pushout-square algebra (Rocq `square` route, Main.v 4180+).
-- Records + cone/comparison/is-pushout/times-I are the DATA both streams
-- agree on.  The two structural theorems are postulated here so Stream A can
-- build against them; Stream B replaces these postulates with proofs (see
-- HANDOFF-lemma26-pushout.md).  comp f g = f ∘ g throughout.
------------------------------------------------------------------------

module Square where

open import Spartan
open import CatAxioms
open import HigherCat using (𝕀)
open import Pullbacks using (_×c_)
open import Product using (product-map; pmc; product-map-eq1)

-- A commuting square in Cat (Rocq `square`).
record Square : Type (𝓤₀ ⁺) where
  constructor mk-square
  field
    sqA sqB sqC sqD : Cat
    sqt : Map sqA sqB
    sql : Map sqA sqC
    sqr : Map sqB sqD
    sqb : Map sqC sqD
    sqcomm : comp sqr sqt ≡ comp sqb sql
open Square public

-- image under Map(–,X): the type-level pullback (Rocq `sq_cone`).
sq-cone : Square → Cat → Type 𝓤₀
sq-cone S X = Σ ge ꞉ (Map (sqC S) X × Map (sqB S) X) ,
                comp (pr₁ ge) (sql S) ≡ comp (pr₂ ge) (sqt S)

-- the comparison Map(sqD,X) → sq-cone (Rocq `sq_comparison`).
sq-comparison : (S : Square) (X : Cat) → Map (sqD S) X → sq-cone S X
sq-comparison S X h =
  (comp h (sqb S) , comp h (sqr S)) ,
  ( composeA h (sqb S) (sql S)
  ∙ ap (comp h) (sqcomm S ⁻¹)
  ∙ (composeA h (sqr S) (sqt S)) ⁻¹ )

-- "S is a pushout" (Rocq `is_pushout_square`; a proposition).
is-pushout-square : Square → Type (𝓤₀ ⁺)
is-pushout-square S = (X : Cat) → is-equiv (sq-comparison S X)

record square-morphism (P Q : Square) : Type 𝓤₀ where
  constructor mk-square-morphism
  field
    smA : Map (sqA P) (sqA Q)
    smB : Map (sqB P) (sqB Q)
    smC : Map (sqC P) (sqC Q)
    smD : Map (sqD P) (sqD Q)
    sm-t : comp (sqt Q) smA ≡ comp smB (sqt P)
    sm-l : comp (sql Q) smA ≡ comp smC (sql P)
    sm-r : comp (sqr Q) smB ≡ comp smD (sqr P)
    sm-b : comp (sqb Q) smC ≡ comp smD (sqb P)
open square-morphism public

record square-retract (S' S : Square) : Type 𝓤₀ where
  constructor mk-square-retract
  field
    sr-s : square-morphism S' S
    sr-r : square-morphism S S'
    sr-A : comp (smA sr-r) (smA sr-s) ≡ idMap (sqA S')
    sr-B : comp (smB sr-r) (smB sr-s) ≡ idMap (sqB S')
    sr-C : comp (smC sr-r) (smC sr-s) ≡ idMap (sqC S')
    sr-D : comp (smD sr-r) (smD sr-s) ≡ idMap (sqD S')
open square-retract public

-- − ×c 𝕀 on squares (Rocq `times_I`).  Commutation from `pmc` (functoriality
-- of product-map): LHS = product-map (sqr∘sqt)(Id∘Id) = product-map (sqb∘sql)(Id∘Id)
-- = RHS, using `sqcomm S`.  (Rocq `times_I`: `rewrite -!pmc; rewrite (sq_comm T)`.)
times-I-comm :
  (S : Square)
  → comp (product-map (sqr S) (idMap 𝕀)) (product-map (sqt S) (idMap 𝕀))
  ≡ comp (product-map (sqb S) (idMap 𝕀)) (product-map (sql S) (idMap 𝕀))
times-I-comm S =
    (pmc (sqt S) (sqr S) (idMap 𝕀) (idMap 𝕀)) ⁻¹
  ∙ product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) (sqcomm S)
  ∙ pmc (sql S) (sqb S) (idMap 𝕀) (idMap 𝕀)

times-I : Square → Square
times-I S = mk-square (sqA S ×c 𝕀) (sqB S ×c 𝕀) (sqC S ×c 𝕀) (sqD S ×c 𝕀)
              (product-map (sqt S) (idMap 𝕀)) (product-map (sql S) (idMap 𝕀))
              (product-map (sqr S) (idMap 𝕀)) (product-map (sqb S) (idMap 𝕀))
              (times-I-comm S)

------------------------------------------------------------------------
-- STREAM B deliverables `is-pushout-square-retract` (Rocq 4655) and
-- `times-I-preserves` (Rocq 6277) are now PROVED in Pushout.agda / TimesI.agda
-- (the former postulate-free; the latter via the cone-reshuffle route).
------------------------------------------------------------------------
