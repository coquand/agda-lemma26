{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — STREAM B: the UNIT law of the cone-pullback functor
-- (Rocq `sq_cone_pre_id`, Main.v 4461, via `unit_leg` = pentagon at Id).
------------------------------------------------------------------------

module ConeUnit where

open import Spartan
open import CatAxioms
open import Coherence
open import SquareAlg

------------------------------------------------------------------------
-- unit-leg (Rocq `unit_leg`): the C/B-side unit coherence, from the two
-- Mac-Lane triangles Id-triangle2 / Id-triangle3 (pentagon-derived).
------------------------------------------------------------------------

unit-leg : {C D E : Cat} (f : Map D E) (k : Map C D)
  → ccl k (comp-id-r f)
  ≡ (composeA f (idMap D) k
     ∙ ccr f ((comp-id-r k ∙ (comp-id-l k) ⁻¹) ⁻¹)
     ∙ (composeA f k (idMap C)) ⁻¹)
    ∙ comp-id-r (comp f k)
unit-leg {C} {D} {E} f k = RHS≡ ⁻¹
  where
  a  = composeA f (idMap D) k
  b  = composeA f k (idMap C)
  P  = ccr f (comp-id-l k)
  Q  = ccr f (comp-id-r k)
  Yk = comp-id-r k ∙ (comp-id-l k) ⁻¹
  u  = comp-id-r (comp f k)

  T2 : a ∙ P ≡ ccl k (comp-id-r f)
  T2 = Id-triangle2 k f

  T3 : b ∙ Q ≡ u
  T3 = Id-triangle3 k f

  stepA : ccr f (Yk ⁻¹) ≡ P ∙ Q ⁻¹
  stepA =
      ap (λ p → ccr f p) (∙-inv (comp-id-r k) ((comp-id-l k) ⁻¹))
    ∙ ap (λ p → ccr f p) (ap (λ z → z ∙ (comp-id-r k) ⁻¹) (⁻¹⁻¹ (comp-id-l k)))
    ∙ ap-∙ (comp f) (comp-id-l k) ((comp-id-r k) ⁻¹)
    ∙ ap (λ z → P ∙ z) (ap-⁻¹ (comp f) (comp-id-r k))

  tail : ((a ∙ (P ∙ Q ⁻¹)) ∙ b ⁻¹) ∙ (b ∙ Q) ≡ a ∙ P
  tail =
      ∙-assoc (a ∙ (P ∙ Q ⁻¹)) (b ⁻¹) (b ∙ Q)
    ∙ ap (λ z → (a ∙ (P ∙ Q ⁻¹)) ∙ z) ((∙-assoc (b ⁻¹) b Q) ⁻¹)
    ∙ ap (λ z → (a ∙ (P ∙ Q ⁻¹)) ∙ (z ∙ Q)) (left-inv b)
    ∙ ∙-assoc a (P ∙ Q ⁻¹) Q
    ∙ ap (λ z → a ∙ z) (∙-assoc P (Q ⁻¹) Q)
    ∙ ap (λ z → a ∙ (P ∙ z)) (left-inv Q)
    ∙ ap (λ z → a ∙ z) (right-unit P)

  RHS≡ : (a ∙ ccr f (Yk ⁻¹) ∙ b ⁻¹) ∙ u ≡ ccl k (comp-id-r f)
  RHS≡ =
      ap (λ z → ((a ∙ z) ∙ b ⁻¹) ∙ u) stepA
    ∙ ap (λ z → ((a ∙ (P ∙ Q ⁻¹)) ∙ b ⁻¹) ∙ z) (T3 ⁻¹)
    ∙ tail
    ∙ T2

------------------------------------------------------------------------
-- sq-cone-pre-id (Rocq `sq_cone_pre_id`).
------------------------------------------------------------------------

sq-cone-pre-id : (S : Square) (X : Cat) (c : sq-cone S X)
               → sq-cone-pre (id-sqm S) X c ≡ c
sq-cone-pre-id S X c = cone-eq {S} {X} {sq-cone-pre (id-sqm S) X c} {c} pg pe coh
  where
  g = cg S X c
  e = ce S X c
  γ = cc S X c

  pg : cg S X (sq-cone-pre (id-sqm S) X c) ≡ cg S X c
  pg = comp-id-r g

  pe : ce S X (sq-cone-pre (id-sqm S) X c) ≡ ce S X c
  pe = comp-id-r e

  R  = ccl (sqt S) (comp-id-r e)
  u1 = comp-id-r (comp g (sql S))
  u2 = comp-id-r (comp e (sqt S))

  reCid : ccl (sql S) (comp-id-r g) ≡ reC (id-sqm S) X c ∙ u1
  reCid = unit-leg g (sql S)

  -- reB-side: reB (id-sqm S) X c ≡ FB ⁻¹, where FB is the unit-leg paren.
  FB = composeA e (idMap (sqB S)) (sqt S)
       ∙ ccr e ((comp-id-r (sqt S) ∙ (comp-id-l (sqt S)) ⁻¹) ⁻¹)
       ∙ (composeA e (sqt S) (idMap (sqA S))) ⁻¹

  Ysqt = comp-id-r (sqt S) ∙ (comp-id-l (sqt S)) ⁻¹

  ULe : R ≡ FB ∙ u2
  ULe = unit-leg e (sqt S)

  M1inv : (ccr e (Ysqt ⁻¹)) ⁻¹ ≡ ccr e Ysqt
  M1inv = ap (λ z → z ⁻¹) (ap-⁻¹ (comp e) Ysqt) ∙ ⁻¹⁻¹ (ccr e Ysqt)

  FBinv≡ : FB ⁻¹
         ≡ composeA e (sqt S) (idMap (sqA S))
           ∙ (ccr e Ysqt ∙ (composeA e (idMap (sqB S)) (sqt S)) ⁻¹)
  FBinv≡ =
      ∙-inv (composeA e (idMap (sqB S)) (sqt S) ∙ ccr e (Ysqt ⁻¹))
            ((composeA e (sqt S) (idMap (sqA S))) ⁻¹)
    ∙ ap (λ z → ((composeA e (sqt S) (idMap (sqA S))) ⁻¹) ⁻¹ ∙ z)
         (∙-inv (composeA e (idMap (sqB S)) (sqt S)) (ccr e (Ysqt ⁻¹)))
    ∙ ap (λ z → z ∙ ((ccr e (Ysqt ⁻¹)) ⁻¹ ∙ (composeA e (idMap (sqB S)) (sqt S)) ⁻¹))
         (⁻¹⁻¹ (composeA e (sqt S) (idMap (sqA S))))
    ∙ ap (λ z → composeA e (sqt S) (idMap (sqA S))
                 ∙ (z ∙ (composeA e (idMap (sqB S)) (sqt S)) ⁻¹))
         M1inv

  flipB : reB (id-sqm S) X c ≡ FB ⁻¹
  flipB =
      ∙-assoc (composeA e (sqt S) (idMap (sqA S))) (ccr e Ysqt)
              ((composeA e (idMap (sqB S)) (sqt S)) ⁻¹)
    ∙ FBinv≡ ⁻¹

  reBidm : u2 ≡ reB (id-sqm S) X c ∙ R
  reBidm =
    ( ap (λ z → z ∙ R) flipB
    ∙ ap (λ z → FB ⁻¹ ∙ z) ULe
    ∙ (∙-assoc (FB ⁻¹) FB u2) ⁻¹
    ∙ ap (λ z → z ∙ u2) (left-inv FB) ) ⁻¹

  coh : ccl (sql S) pg ∙ cc S X c
      ≡ cc S X (sq-cone-pre (id-sqm S) X c) ∙ ccl (sqt S) pe
  coh =
      ap (λ z → z ∙ γ) reCid
    ∙ ∙-assoc (reC (id-sqm S) X c) u1 γ
    ∙ ap (λ z → reC (id-sqm S) X c ∙ z) (IdKr-nat γ)
    ∙ ap (λ z → reC (id-sqm S) X c ∙ (ccl (idMap (sqA S)) γ ∙ z)) reBidm
    ∙ (   ∙-assoc (reC (id-sqm S) X c ∙ ccl (idMap (sqA S)) γ)
                  (reB (id-sqm S) X c) R
        ∙ ∙-assoc (reC (id-sqm S) X c) (ccl (idMap (sqA S)) γ)
                  (reB (id-sqm S) X c ∙ R) ) ⁻¹
