{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — STREAM B: NATURALITY of the comparison map w.r.t. square
-- morphisms (Rocq `sq_comparison_natural`, Main.v 4600, "the cube":
-- reduces via shape1/shape2/pentL to `cube_corner`, discharged by the
-- isaset corner hypothesis).
------------------------------------------------------------------------

module Squares.ConeNat where

open import Foundations.Spartan
open import Category.CatAxioms
open import Foundations.Coherence
open import Solvers.CayleyAssoc
open import Squares.SquareAlg

------------------------------------------------------------------------
-- groupoid / pentagon helpers (Rocq `cancl`, `shape1`, `shape2`, `pentL`,
-- `cube_corner`).
------------------------------------------------------------------------

-- Rocq `cancl`:  ! p @ (p @ q) = q.
cancl : {A : Type 𝓤} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ⁻¹ ∙ (p ∙ q) ≡ q
cancl (refl _) q = refl q

-- Rocq `cube_corner`: equal-endpoint paths in a (set) corner hom coincide.
cube-corner : {P Q : Square} (m : square-morphism P Q)
  (HD : is-set (Map (sqA P) (sqD Q)))
  {p q : Map (sqA P) (sqD Q)} (u v : p ≡ q) → u ≡ v
cube-corner m HD {p} {q} u v = HD p q u v

-- Rocq `shape1`: pull h outermost (h-outermost normal form), C-side.
shape1 : {A0 A B Xc : Cat} (f : Map B Xc) (c : Map A0 A) {g g' : Map A B} (F : g ≡ g')
  → ap (λ w → comp (comp f w) c) F
  ≡ composeA f g c ∙ ccr f (ccl c F) ∙ (composeA f g' c) ⁻¹
shape1 f c {g} (refl _) =
  ( ap (λ z → z ∙ (composeA f g c) ⁻¹) (right-unit (composeA f g c))
    ∙ right-inv (composeA f g c) ) ⁻¹

-- Rocq `shape2`: pull h outermost, B-side.
shape2 : {A0 A B Xc : Cat} (f : Map B Xc) (g : Map A B) {hh hh' : Map A0 A} (F : hh ≡ hh')
  → ap (λ w → comp (comp f g) w) F
  ≡ composeA f g hh ∙ ccr f (ccr g F) ∙ (composeA f g hh') ⁻¹
shape2 f g {hh} (refl _) =
  ( ap (λ z → z ∙ (composeA f g hh) ⁻¹) (right-unit (composeA f g hh))
    ∙ right-inv (composeA f g hh) ) ⁻¹

-- Rocq `pentL`: the left-pentagon normal form of a degenerate triple.
pentL : {A B C D E : Cat} (f : Map D E) (g : Map C D) (hh : Map B C) (e : Map A B)
  → composeA (comp f g) hh e
  ≡ (ccl e (composeA f g hh) ∙ composeA f (comp g hh) e)
    ∙ ccr f (composeA g hh e)
    ∙ (composeA f g (comp hh e)) ⁻¹
pentL f g hh e =
    (right-unit (composeA (comp f g) hh e)) ⁻¹
  ∙ ap (λ z → composeA (comp f g) hh e ∙ z)
       ((right-inv (composeA f g (comp hh e))) ⁻¹)
  ∙ (∙-assoc (composeA (comp f g) hh e) (composeA f g (comp hh e))
             ((composeA f g (comp hh e)) ⁻¹)) ⁻¹
  ∙ ap (λ z → z ∙ (composeA f g (comp hh e)) ⁻¹) (pentagonator f g hh e)

-- The cube reduction (Rocq `sq_comparison_natural`): via `cone-eq` with
--   pg = composeA h (smD m)(sqb P) ∙ ccr h (sm-b m ⁻¹) ∙ (composeA h (sqb Q)(smC m))⁻¹
--   pe = composeA h (smD m)(sqr P) ∙ ccr h (sm-r m ⁻¹) ∙ (composeA h (sqr Q)(smB m))⁻¹
-- both LH and RH reduce (shape1/shape2/pentL to h-outermost form, then cancl the
-- frame reassociators) to the common frame `X1 ∙ X2 ∙ ap (comp h) (·) ∙ Y2 ∙ Y1`
-- whose inner `·` lives in the corner hom `Map (sqA P)(sqD Q)`; since that is a set
-- (HD), `cube-corner m HD` identifies the two inner paths.  Now PROVED below.
sq-comparison-natural :
  {P Q : Square} (m : square-morphism P Q) (X : Cat)
  (HD : is-set (Map (sqA P) (sqD Q))) (h : Map (sqD Q) X)
  → sq-comparison P X (sq-apex-pre m X h) ≡ sq-cone-pre m X (sq-comparison Q X h)
sq-comparison-natural {P} {Q} m X HD h =
  cone-eq {P} {X}
    {sq-comparison P X (sq-apex-pre m X h)}
    {sq-cone-pre m X (sq-comparison Q X h)}
    pg pe coh
  where
  pg : cg P X (sq-comparison P X (sq-apex-pre m X h))
     ≡ cg P X (sq-cone-pre m X (sq-comparison Q X h))
  pg = composeA h (smD m) (sqb P) ∙ ccr h ((sm-b m) ⁻¹)
       ∙ (composeA h (sqb Q) (smC m)) ⁻¹

  pe : ce P X (sq-comparison P X (sq-apex-pre m X h))
     ≡ ce P X (sq-cone-pre m X (sq-comparison Q X h))
  pe = composeA h (smD m) (sqr P) ∙ ccr h ((sm-r m) ⁻¹)
       ∙ (composeA h (sqr Q) (smB m)) ⁻¹

  ----------------------------------------------------------------------
  -- abbreviations
  ----------------------------------------------------------------------
  bP = sqb P
  lP = sql P
  rP = sqr P
  tP = sqt P
  bQ = sqb Q
  lQ = sql Q
  rQ = sqr Q
  tQ = sqt Q
  mA = smA m
  mB = smB m
  mC = smC m
  mD = smD m

  ----------------------------------------------------------------------
  -- common frame:  X1 ∙ X2 ∙ ap(comp h) u ∙ Y2 ∙ Y1
  ----------------------------------------------------------------------
  X1 = ccl lP (composeA h mD bP)
  X2 = composeA h (comp mD bP) lP
  Y2 = (composeA h (comp rQ mB) tP) ⁻¹
  Y1 = ccl tP ((composeA h rQ mB) ⁻¹)

  FR : comp (comp mD bP) lP ≡ comp (comp rQ mB) tP
     → comp (comp (comp h mD) bP) lP ≡ comp (comp (comp h rQ) mB) tP
  FR u = X1 ∙ (X2 ∙ (ap (comp h) u ∙ (Y2 ∙ Y1)))

  ----------------------------------------------------------------------
  -- RH side:  cc P X (cLHS) ∙ ccl tP pe  ≡  FR uR
  ----------------------------------------------------------------------
  A1 = ccr h (composeA mD bP lP)
  A2 = ccr h (ccr mD (sqcomm P ⁻¹))
  Z1 = ccl tP (composeA h mD rP)
  Z2 = composeA h (comp mD rP) tP
  Z3 = ccr h (composeA mD rP tP)
  B1 = composeA h mD (comp bP lP)
  B2 = composeA h mD (comp rP tP)
  D4 = ccr h (ccl tP ((sm-r m) ⁻¹))
  C4 = ccl tP (ccr h ((sm-r m) ⁻¹))

  RA = composeA (comp h mD) bP lP
  RB = ap (comp (comp h mD)) (sqcomm P ⁻¹)
  RC = (composeA (comp h mD) rP tP) ⁻¹
  RD = ccl tP pe

  RAx = ((X1 ∙ X2) ∙ A1) ∙ B1 ⁻¹
  RBx = (B1 ∙ A2) ∙ B2 ⁻¹
  RCx = B2 ∙ (Z3 ⁻¹ ∙ (Z2 ⁻¹ ∙ Z1 ⁻¹))
  RDx = (Z1 ∙ C4) ∙ Y1

  uR = composeA mD bP lP
     ∙ (ccr mD (sqcomm P ⁻¹) ∙ ((composeA mD rP tP) ⁻¹ ∙ ccl tP ((sm-r m) ⁻¹)))

  eqRA : RA ≡ RAx
  eqRA = pentL h mD bP lP

  eqRB : RB ≡ RBx
  eqRB = shape2 h mD (sqcomm P ⁻¹)

  eqRC : RC ≡ RCx
  eqRC =
      ap _⁻¹ (pentL h mD rP tP)
    ∙ ∙-inv (((Z1 ∙ Z2) ∙ Z3)) (B2 ⁻¹)
    ∙ ap (λ z → z ∙ ((Z1 ∙ Z2) ∙ Z3) ⁻¹) (⁻¹⁻¹ B2)
    ∙ ap (λ z → B2 ∙ z) (∙-inv (Z1 ∙ Z2) Z3)
    ∙ ap (λ z → B2 ∙ (Z3 ⁻¹ ∙ z)) (∙-inv Z1 Z2)

  eqRD : RD ≡ RDx
  eqRD =
      ap-∙ (λ w → comp w tP) (composeA h mD rP ∙ ccr h ((sm-r m) ⁻¹))
           ((composeA h rQ mB) ⁻¹)
    ∙ ap (λ z → z ∙ Y1)
         (ap-∙ (λ w → comp w tP) (composeA h mD rP) (ccr h ((sm-r m) ⁻¹)))

  eqC4 : C4 ≡ (Z2 ∙ D4) ∙ Y2
  eqC4 = ap-comp (λ w → comp w tP) (comp h) ((sm-r m) ⁻¹)
       ∙ shape1 h tP ((sm-r m) ⁻¹)

  combineR : ap (comp h) uR ≡ A1 ∙ (A2 ∙ (Z3 ⁻¹ ∙ D4))
  combineR =
      ap-∙ (comp h) (composeA mD bP lP)
           (ccr mD (sqcomm P ⁻¹) ∙ ((composeA mD rP tP) ⁻¹ ∙ ccl tP ((sm-r m) ⁻¹)))
    ∙ ap (λ z → A1 ∙ z)
         (ap-∙ (comp h) (ccr mD (sqcomm P ⁻¹))
               ((composeA mD rP tP) ⁻¹ ∙ ccl tP ((sm-r m) ⁻¹)))
    ∙ ap (λ z → A1 ∙ (A2 ∙ z))
         (ap-∙ (comp h) ((composeA mD rP tP) ⁻¹) (ccl tP ((sm-r m) ⁻¹)))
    ∙ ap (λ z → A1 ∙ (A2 ∙ (z ∙ D4))) (ap-⁻¹ (comp h) (composeA mD rP tP))

  RST1 = A2 ∙ (B2 ⁻¹ ∙ (B2 ∙ (Z3 ⁻¹ ∙ (Z2 ⁻¹ ∙ (Z1 ⁻¹ ∙ (Z1 ∙ (Z2 ∙ (D4 ∙ (Y2 ∙ Y1)))))))))
  RST2 = Z3 ⁻¹ ∙ (Z2 ⁻¹ ∙ (Z1 ⁻¹ ∙ (Z1 ∙ (Z2 ∙ (D4 ∙ (Y2 ∙ Y1))))))
  RST3 = Z2 ∙ (D4 ∙ (Y2 ∙ Y1))
  RST4 = D4 ∙ (Y2 ∙ Y1)

  rhsNF : cc P X (sq-comparison P X (sq-apex-pre m X h)) ∙ ccl (sqt P) pe ≡ FR uR
  rhsNF =
      ap (λ z → ((z ∙ RB) ∙ RC) ∙ RD) eqRA
    ∙ ap (λ z → ((RAx ∙ z) ∙ RC) ∙ RD) eqRB
    ∙ ap (λ z → ((RAx ∙ RBx) ∙ z) ∙ RD) eqRC
    ∙ ap (λ z → ((RAx ∙ RBx) ∙ RCx) ∙ z) eqRD
    ∙ ap (λ z → ((RAx ∙ RBx) ∙ RCx) ∙ ((Z1 ∙ z) ∙ Y1)) eqC4
    ∙ solveR
        ((((((ι X1 ⊕ ι X2) ⊕ ι A1) ⊕ ι (B1 ⁻¹))
            ⊕ ((ι B1 ⊕ ι A2) ⊕ ι (B2 ⁻¹)))
           ⊕ (ι B2 ⊕ (ι (Z3 ⁻¹) ⊕ (ι (Z2 ⁻¹) ⊕ ι (Z1 ⁻¹)))))
          ⊕ ((ι Z1 ⊕ ((ι Z2 ⊕ ι D4) ⊕ ι Y2)) ⊕ ι Y1))
        (ι X1 ⊕ (ι X2 ⊕ (ι A1 ⊕ (ι (B1 ⁻¹) ⊕ (ι B1 ⊕ (ι A2 ⊕ (ι (B2 ⁻¹) ⊕ (ι B2 ⊕
          (ι (Z3 ⁻¹) ⊕ (ι (Z2 ⁻¹) ⊕ (ι (Z1 ⁻¹) ⊕ (ι Z1 ⊕ (ι Z2 ⊕ (ι D4 ⊕ (ι Y2 ⊕ ι Y1)))))))))))))))
        (refl _)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (A1 ∙ z))) (cancl B1 RST1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (A1 ∙ (A2 ∙ z)))) (cancl B2 RST2)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (A1 ∙ (A2 ∙ (Z3 ⁻¹ ∙ (Z2 ⁻¹ ∙ z)))))) (cancl Z1 RST3)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (A1 ∙ (A2 ∙ (Z3 ⁻¹ ∙ z))))) (cancl Z2 RST4)
    ∙ solveR
        ( ι X1 ⊕ (ι X2 ⊕ (ι A1 ⊕ (ι A2 ⊕ (ι (Z3 ⁻¹) ⊕ (ι D4 ⊕ (ι Y2 ⊕ ι Y1)))))) )
        ( ι X1 ⊕ (ι X2 ⊕ ((ι A1 ⊕ (ι A2 ⊕ (ι (Z3 ⁻¹) ⊕ ι D4))) ⊕ (ι Y2 ⊕ ι Y1))) )
        (refl _)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (z ∙ (Y2 ∙ Y1)))) (combineR ⁻¹)

  ----------------------------------------------------------------------
  -- LH side:  ccl lP pg ∙ cc P X (cRHS)  ≡  FR uL
  ----------------------------------------------------------------------
  Pb = ccl lP (ccr h ((sm-b m) ⁻¹))
  Pc = ccl lP ((composeA h bQ mC) ⁻¹)
  PcPos = ccl lP (composeA h bQ mC)
  E1 = composeA h (comp bQ mC) lP
  Db = ccr h (ccl lP ((sm-b m) ⁻¹))
  Ac = ccr h (composeA bQ mC lP)
  Bc = ccr h (ccr bQ ((sm-l m) ⁻¹))
  Cc = ccr h (composeA bQ lQ mA)
  G1 = composeA h bQ (comp mC lP)
  G2 = composeA h bQ (comp lQ mA)
  H1 = ccl mA (composeA h bQ lQ)
  H2 = composeA h (comp bQ lQ) mA
  Dq = ccr h (ccl mA (sqcomm Q ⁻¹))
  I1 = composeA h (comp rQ tQ) mA
  Q3Pos = ccl mA (composeA h rQ tQ)
  Ae = ccr h (composeA rQ tQ mA)
  Be = ccr h (ccr rQ (sm-t m))
  Ce = ccr h (composeA rQ mB tP)
  K1 = composeA h rQ (comp tQ mA)
  K2 = composeA h rQ (comp mB tP)
  L1 = ccl tP (composeA h rQ mB)
  L2 = composeA h (comp rQ mB) tP
  Q2 = ccl mA (ap (comp h) (sqcomm Q ⁻¹))
  Q3 = ccl mA ((composeA h rQ tQ) ⁻¹)

  LP = ccl lP pg
  firstC = composeA (comp h bQ) mC lP
  midC = ccr (comp h bQ) ((sm-l m) ⁻¹)
  lastC = (composeA (comp h bQ) lQ mA) ⁻¹
  reCm = reC m X (sq-comparison Q X h)
  Mqm = ccl mA (cc Q X (sq-comparison Q X h))
  firstB = composeA (comp h rQ) tQ mA
  midB = ccr (comp h rQ) (sm-t m)
  lastB = (composeA (comp h rQ) mB tP) ⁻¹
  reBm = reB m X (sq-comparison Q X h)

  -- expanded forms
  firstCx = ((PcPos ∙ E1) ∙ Ac) ∙ G1 ⁻¹
  midCx = (G1 ∙ Bc) ∙ G2 ⁻¹
  lastCx = G2 ∙ (Cc ⁻¹ ∙ (H2 ⁻¹ ∙ H1 ⁻¹))
  reCx = (firstCx ∙ midCx) ∙ lastCx
  Q2x = (H2 ∙ Dq) ∙ I1 ⁻¹
  Mqx = (H1 ∙ Q2x) ∙ Q3Pos ⁻¹
  firstBx = ((Q3Pos ∙ I1) ∙ Ae) ∙ K1 ⁻¹
  midBx = (K1 ∙ Be) ∙ K2 ⁻¹
  lastBx = K2 ∙ (Ce ⁻¹ ∙ (L2 ⁻¹ ∙ L1 ⁻¹))
  reBx = (firstBx ∙ midBx) ∙ lastBx
  LPx = (X1 ∙ ((X2 ∙ Db) ∙ E1 ⁻¹)) ∙ PcPos ⁻¹

  uL = ccl lP ((sm-b m) ⁻¹)
     ∙ (composeA bQ mC lP
       ∙ (ccr bQ ((sm-l m) ⁻¹)
         ∙ ((composeA bQ lQ mA) ⁻¹
           ∙ (ccl mA (sqcomm Q ⁻¹)
             ∙ (composeA rQ tQ mA
               ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹))))))

  eqPb : Pb ≡ (X2 ∙ Db) ∙ E1 ⁻¹
  eqPb = ap-comp (λ w → comp w lP) (comp h) ((sm-b m) ⁻¹)
       ∙ shape1 h lP ((sm-b m) ⁻¹)

  eqPc : Pc ≡ PcPos ⁻¹
  eqPc = ap-⁻¹ (λ w → comp w lP) (composeA h bQ mC)

  eqLP : LP ≡ LPx
  eqLP =
      ( ap-∙ (λ w → comp w lP) (composeA h mD bP ∙ ccr h ((sm-b m) ⁻¹))
             ((composeA h bQ mC) ⁻¹)
      ∙ ap (λ z → z ∙ Pc)
           (ap-∙ (λ w → comp w lP) (composeA h mD bP) (ccr h ((sm-b m) ⁻¹))) )
    ∙ ap (λ z → (X1 ∙ z) ∙ Pc) eqPb
    ∙ ap (λ z → (X1 ∙ ((X2 ∙ Db) ∙ E1 ⁻¹)) ∙ z) eqPc

  eqfirstC : firstC ≡ firstCx
  eqfirstC = pentL h bQ mC lP

  eqmidC : midC ≡ midCx
  eqmidC = shape2 h bQ ((sm-l m) ⁻¹)

  eqlastC : lastC ≡ lastCx
  eqlastC =
      ap _⁻¹ (pentL h bQ lQ mA)
    ∙ ∙-inv ((H1 ∙ H2) ∙ Cc) (G2 ⁻¹)
    ∙ ap (λ z → z ∙ ((H1 ∙ H2) ∙ Cc) ⁻¹) (⁻¹⁻¹ G2)
    ∙ ap (λ z → G2 ∙ z) (∙-inv (H1 ∙ H2) Cc)
    ∙ ap (λ z → G2 ∙ (Cc ⁻¹ ∙ z)) (∙-inv H1 H2)

  eqReC : reCm ≡ reCx
  eqReC = ap (λ z → (z ∙ midC) ∙ lastC) eqfirstC
        ∙ ap (λ z → (firstCx ∙ z) ∙ lastC) eqmidC
        ∙ ap (λ z → (firstCx ∙ midCx) ∙ z) eqlastC

  eqQ2 : Q2 ≡ Q2x
  eqQ2 = ap-comp (λ w → comp w mA) (comp h) (sqcomm Q ⁻¹)
       ∙ shape1 h mA (sqcomm Q ⁻¹)

  eqQ3 : Q3 ≡ Q3Pos ⁻¹
  eqQ3 = ap-⁻¹ (λ w → comp w mA) (composeA h rQ tQ)

  eqMq : Mqm ≡ Mqx
  eqMq =
      ( ap-∙ (λ w → comp w mA) (composeA h bQ lQ ∙ ap (comp h) (sqcomm Q ⁻¹))
             ((composeA h rQ tQ) ⁻¹)
      ∙ ap (λ z → z ∙ Q3)
           (ap-∙ (λ w → comp w mA) (composeA h bQ lQ) (ap (comp h) (sqcomm Q ⁻¹))) )
    ∙ ap (λ z → (H1 ∙ z) ∙ Q3) eqQ2
    ∙ ap (λ z → (H1 ∙ Q2x) ∙ z) eqQ3

  eqfirstB : firstB ≡ firstBx
  eqfirstB = pentL h rQ tQ mA

  eqmidB : midB ≡ midBx
  eqmidB = shape2 h rQ (sm-t m)

  eqlastB : lastB ≡ lastBx
  eqlastB =
      ap _⁻¹ (pentL h rQ mB tP)
    ∙ ∙-inv ((L1 ∙ L2) ∙ Ce) (K2 ⁻¹)
    ∙ ap (λ z → z ∙ ((L1 ∙ L2) ∙ Ce) ⁻¹) (⁻¹⁻¹ K2)
    ∙ ap (λ z → K2 ∙ z) (∙-inv (L1 ∙ L2) Ce)
    ∙ ap (λ z → K2 ∙ (Ce ⁻¹ ∙ z)) (∙-inv L1 L2)

  eqReB : reBm ≡ reBx
  eqReB = ap (λ z → (z ∙ midB) ∙ lastB) eqfirstB
        ∙ ap (λ z → (firstBx ∙ z) ∙ lastB) eqmidB
        ∙ ap (λ z → (firstBx ∙ midBx) ∙ z) eqlastB

  convL1 : L1 ⁻¹ ≡ Y1
  convL1 = (ap-⁻¹ (λ w → comp w tP) (composeA h rQ mB)) ⁻¹

  combineL : ap (comp h) uL ≡ Db ∙ (Ac ∙ (Bc ∙ (Cc ⁻¹ ∙ (Dq ∙ (Ae ∙ (Be ∙ Ce ⁻¹))))))
  combineL =
      ap-∙ (comp h) (ccl lP ((sm-b m) ⁻¹))
           (composeA bQ mC lP ∙ (ccr bQ ((sm-l m) ⁻¹) ∙ ((composeA bQ lQ mA) ⁻¹
             ∙ (ccl mA (sqcomm Q ⁻¹) ∙ (composeA rQ tQ mA
               ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹))))))
    ∙ ap (λ z → Db ∙ z)
         (ap-∙ (comp h) (composeA bQ mC lP)
           (ccr bQ ((sm-l m) ⁻¹) ∙ ((composeA bQ lQ mA) ⁻¹
             ∙ (ccl mA (sqcomm Q ⁻¹) ∙ (composeA rQ tQ mA
               ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹))))))
    ∙ ap (λ z → Db ∙ (Ac ∙ z))
         (ap-∙ (comp h) (ccr bQ ((sm-l m) ⁻¹))
           ((composeA bQ lQ mA) ⁻¹ ∙ (ccl mA (sqcomm Q ⁻¹) ∙ (composeA rQ tQ mA
             ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹)))))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ z)))
         (ap-∙ (comp h) ((composeA bQ lQ mA) ⁻¹)
           (ccl mA (sqcomm Q ⁻¹) ∙ (composeA rQ tQ mA
             ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹))))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ (ap (comp h) ((composeA bQ lQ mA) ⁻¹) ∙ z))))
         (ap-∙ (comp h) (ccl mA (sqcomm Q ⁻¹))
           (composeA rQ tQ mA ∙ (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹)))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ (ap (comp h) ((composeA bQ lQ mA) ⁻¹) ∙ (Dq ∙ z)))))
         (ap-∙ (comp h) (composeA rQ tQ mA)
           (ccr rQ (sm-t m) ∙ (composeA rQ mB tP) ⁻¹))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ (ap (comp h) ((composeA bQ lQ mA) ⁻¹) ∙ (Dq ∙ (Ae ∙ z))))))
         (ap-∙ (comp h) (ccr rQ (sm-t m)) ((composeA rQ mB tP) ⁻¹))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ (z ∙ (Dq ∙ (Ae ∙ (Be ∙ ap (comp h) ((composeA rQ mB tP) ⁻¹))))))))
         (ap-⁻¹ (comp h) (composeA bQ lQ mA))
    ∙ ap (λ z → Db ∙ (Ac ∙ (Bc ∙ (Cc ⁻¹ ∙ (Dq ∙ (Ae ∙ (Be ∙ z)))))))
         (ap-⁻¹ (comp h) (composeA rQ mB tP))

  qPc = E1 ∙ (Ac ∙ ((G1 ⁻¹) ∙ (G1 ∙ (Bc ∙ ((G2 ⁻¹) ∙ (G2 ∙ ((Cc ⁻¹) ∙ ((H2 ⁻¹) ∙ ((H1 ⁻¹) ∙ (H1 ∙ (H2 ∙ (Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹))))))))))))))))))))))))))
  qE1 = Ac ∙ ((G1 ⁻¹) ∙ (G1 ∙ (Bc ∙ ((G2 ⁻¹) ∙ (G2 ∙ ((Cc ⁻¹) ∙ ((H2 ⁻¹) ∙ ((H1 ⁻¹) ∙ (H1 ∙ (H2 ∙ (Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹)))))))))))))))))))))))))
  qG1 = Bc ∙ ((G2 ⁻¹) ∙ (G2 ∙ ((Cc ⁻¹) ∙ ((H2 ⁻¹) ∙ ((H1 ⁻¹) ∙ (H1 ∙ (H2 ∙ (Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹))))))))))))))))))))))
  qG2 = (Cc ⁻¹) ∙ ((H2 ⁻¹) ∙ ((H1 ⁻¹) ∙ (H1 ∙ (H2 ∙ (Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹)))))))))))))))))))
  qH1 = H2 ∙ (Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹)))))))))))))))
  qH2 = Dq ∙ ((I1 ⁻¹) ∙ ((Q3Pos ⁻¹) ∙ (Q3Pos ∙ (I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹))))))))))))))
  qQ3Pos = I1 ∙ (Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹))))))))))
  qI1 = Ae ∙ ((K1 ⁻¹) ∙ (K1 ∙ (Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹)))))))))
  qK1 = Be ∙ ((K2 ⁻¹) ∙ (K2 ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹))))))
  qK2 = (Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ ((L1 ⁻¹)))

  lhsNF : ccl (sql P) pg ∙ cc P X (sq-cone-pre m X (sq-comparison Q X h)) ≡ FR uL
  lhsNF =
      ap (λ z → z ∙ ((reCm ∙ Mqm) ∙ reBm)) eqLP
    ∙ ap (λ z → LPx ∙ ((z ∙ Mqm) ∙ reBm)) eqReC
    ∙ ap (λ z → LPx ∙ ((reCx ∙ z) ∙ reBm)) eqMq
    ∙ ap (λ z → LPx ∙ ((reCx ∙ Mqx) ∙ z)) eqReB
    ∙ solveR
        (((ι X1 ⊕ ((ι X2 ⊕ ι Db) ⊕ ι (E1 ⁻¹))) ⊕ ι (PcPos ⁻¹)) ⊕ (((((((ι PcPos ⊕ ι E1) ⊕ ι Ac) ⊕ ι (G1 ⁻¹)) ⊕ ((ι G1 ⊕ ι Bc) ⊕ ι (G2 ⁻¹))) ⊕ (ι G2 ⊕ (ι (Cc ⁻¹) ⊕ (ι (H2 ⁻¹) ⊕ ι (H1 ⁻¹))))) ⊕ ((ι H1 ⊕ ((ι H2 ⊕ ι Dq) ⊕ ι (I1 ⁻¹))) ⊕ ι (Q3Pos ⁻¹))) ⊕ (((((ι Q3Pos ⊕ ι I1) ⊕ ι Ae) ⊕ ι (K1 ⁻¹)) ⊕ ((ι K1 ⊕ ι Be) ⊕ ι (K2 ⁻¹))) ⊕ (ι K2 ⊕ (ι (Ce ⁻¹) ⊕ (ι (L2 ⁻¹) ⊕ ι (L1 ⁻¹)))))))
        (ι X1 ⊕ (ι X2 ⊕ (ι Db ⊕ (ι (E1 ⁻¹) ⊕ (ι (PcPos ⁻¹) ⊕ (ι PcPos ⊕ (ι E1 ⊕ (ι Ac ⊕ (ι (G1 ⁻¹) ⊕ (ι G1 ⊕ (ι Bc ⊕ (ι (G2 ⁻¹) ⊕ (ι G2 ⊕ (ι (Cc ⁻¹) ⊕ (ι (H2 ⁻¹) ⊕ (ι (H1 ⁻¹) ⊕ (ι H1 ⊕ (ι H2 ⊕ (ι Dq ⊕ (ι (I1 ⁻¹) ⊕ (ι (Q3Pos ⁻¹) ⊕ (ι Q3Pos ⊕ (ι I1 ⊕ (ι Ae ⊕ (ι (K1 ⁻¹) ⊕ (ι K1 ⊕ (ι Be ⊕ (ι (K2 ⁻¹) ⊕ (ι K2 ⊕ (ι (Ce ⁻¹) ⊕ (ι (L2 ⁻¹) ⊕ ι (L1 ⁻¹))))))))))))))))))))))))))))))))
        (refl _)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ ((E1 ⁻¹) ∙ z)))) (cancl PcPos qPc)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ z))) (cancl E1 qE1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ z)))) (cancl G1 qG1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ z))))) (cancl G2 qG2)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ ((H2 ⁻¹) ∙ z))))))) (cancl H1 qH1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ z)))))) (cancl H2 qH2)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ (Dq ∙ ((I1 ⁻¹) ∙ z)))))))) (cancl Q3Pos qQ3Pos)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ (Dq ∙ z))))))) (cancl I1 qI1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ (Dq ∙ (Ae ∙ z)))))))) (cancl K1 qK1)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ (Dq ∙ (Ae ∙ (Be ∙ z))))))))) (cancl K2 qK2)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (Db ∙ (Ac ∙ (Bc ∙ ((Cc ⁻¹) ∙ (Dq ∙ (Ae ∙ (Be ∙ ((Ce ⁻¹) ∙ ((L2 ⁻¹) ∙ z))))))))))) convL1
    ∙ solveR
        (ι X1 ⊕ (ι X2 ⊕ (ι Db ⊕ (ι Ac ⊕ (ι Bc ⊕ (ι (Cc ⁻¹) ⊕ (ι Dq ⊕ (ι Ae ⊕ (ι Be ⊕ (ι (Ce ⁻¹) ⊕ (ι Y2 ⊕ ι Y1)))))))))))
        (ι X1 ⊕ (ι X2 ⊕ ((ι Db ⊕ (ι Ac ⊕ (ι Bc ⊕ (ι (Cc ⁻¹) ⊕ (ι Dq ⊕ (ι Ae ⊕ (ι Be ⊕ ι (Ce ⁻¹)))))))) ⊕ (ι Y2 ⊕ ι Y1))))
        (refl _)
    ∙ ap (λ z → X1 ∙ (X2 ∙ (z ∙ (Y2 ∙ Y1)))) (combineL ⁻¹)

  coh : ccl (sql P) pg ∙ cc P X (sq-cone-pre m X (sq-comparison Q X h))
      ≡ cc P X (sq-comparison P X (sq-apex-pre m X h)) ∙ ccl (sqt P) pe
  coh = lhsNF ∙ ap (λ z → FR z) (cube-corner m HD uL uR) ∙ rhsNF ⁻¹
