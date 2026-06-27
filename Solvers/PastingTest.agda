{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Stage 2 end-to-end test: reproduce LUCIE `injr_unit_loop` (dsl_C.v)
-- entirely in the pasting DSL.
--
-- The Rocq lemma fixes i := injr, but the proof never uses any property
-- of injr: it is a pure unit-coherence loop, valid for ANY 1-cell i.
-- In raw form it is a ~40-line `S8` telescope; here it is four named
-- moves — tri1, tri1, ul-nat — plus inverse cancellation.
------------------------------------------------------------------------

module Solvers.PastingTest where

open import Foundations.Spartan
open import Category.CatAxioms
open import Foundations.Coherence
open import Solvers.PastingDSL

injr-unit-loop : {x y : Cat} (i : Map x y)
  → sy (rw (comp (idMap y) i) (ul (idMap y)))
    ⊙ al (idMap y) (idMap y) (comp (idMap y) i)
    ⊙ sy (lw (idMap y) (al (idMap y) (idMap y) i))
    ⊙ lw (idMap y) (rw i (ul (idMap y)))
  ≡ idc (comp (idMap y) (comp (idMap y) i))
injr-unit-loop {x} {y} i =
    ap (λ z → A ⊙ B ⊙ z) step1
  ∙ ap (λ z → A ⊙ z) step2
  ∙ cancL (rw IDi (ul Iy)) (sy (ul big) ⊙ lw Iy (ul IDi))
  ∙ ap (λ z → sy z ⊙ lw Iy (ul IDi)) E3
  ∙ vinvL (lw Iy (ul IDi))
  where
  Iy  = idMap y
  IDi = comp Iy i
  big = comp Iy IDi
  A   = sy (rw IDi (ul Iy))
  B   = al Iy Iy IDi

  -- bottom leg: rw i (ul Id) is a triangle; whisker it, cancel the assoc.
  step1 : sy (lw Iy (al Iy Iy i)) ⊙ lw Iy (rw i (ul Iy)) ≡ lw Iy (ul IDi)
  step1 =
      ap (λ z → sy (lw Iy (al Iy Iy i)) ⊙ z)
         (ap (lw Iy) ((tri1 i Iy) ⁻¹) ∙ lw-vc Iy (al Iy Iy i) (ul IDi))
    ∙ cancL (lw Iy (al Iy Iy i)) (lw Iy (ul IDi))

  -- the associator B = al Id Id (Id∘i) solved for its unitor leg (tri1).
  E4 : B ≡ rw IDi (ul Iy) ⊙ sy (ul big)
  E4 = strip-r (ul big)
         (tri1 IDi Iy
           ∙ ( (vassoc (rw IDi (ul Iy)) (sy (ul big)) (ul big)) ⁻¹
             ∙ ap (λ z → rw IDi (ul Iy) ⊙ z) (vinvL (ul big))
             ∙ vidr (rw IDi (ul Iy)) ) ⁻¹)

  step2 : B ⊙ lw Iy (ul IDi)
        ≡ rw IDi (ul Iy) ⊙ sy (ul big) ⊙ lw Iy (ul IDi)
  step2 = ap (λ z → z ⊙ lw Iy (ul IDi)) E4
        ∙ (vassoc (rw IDi (ul Iy)) (sy (ul big)) (lw Iy (ul IDi))) ⁻¹

  -- the two stacked unitors agree by unitor-naturality.
  E3 : ul big ≡ lw Iy (ul IDi)
  E3 = strip-r (ul IDi) (ul-nat (ul IDi))
