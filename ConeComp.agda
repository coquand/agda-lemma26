{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — STREAM B: the COMPOSITION law of the cone-pullback functor
-- (Rocq `sq_cone_pre_comp`, Main.v ~4500, the genuine pentagon use via
-- `releg_comp`).
------------------------------------------------------------------------

module ConeComp where

open import Spartan
open import CatAxioms
open import Coherence
open import CayleyAssoc
open import SquareAlg

------------------------------------------------------------------------
-- groupoid helpers (Rocq slide / flipinv / mp_homot)
------------------------------------------------------------------------

-- Rocq `slide`:  a ∙ p ≡ q ∙ b  →  b ∙ p⁻¹ ≡ q⁻¹ ∙ a.
slide : {X : Type 𝓤} {w x y z : X}
        (a : w ≡ x) (p : x ≡ z) (q : w ≡ y) (b : y ≡ z)
      → a ∙ p ≡ q ∙ b → b ∙ p ⁻¹ ≡ q ⁻¹ ∙ a
slide a p q b H =
  cancel-left q
    ( (∙-assoc q b (p ⁻¹)) ⁻¹
      ∙ ap (λ z → z ∙ p ⁻¹) (H ⁻¹)
      ∙ ∙-assoc a p (p ⁻¹)
      ∙ ap (λ z → a ∙ z) (right-inv p)
      ∙ right-unit a
      ∙ (ap (λ z → z ∙ a) (right-inv q)) ⁻¹
      ∙ ∙-assoc q (q ⁻¹) a )

-- Rocq `flipinv`:  a ∙ x ≡ y  →  x⁻¹ ≡ y⁻¹ ∙ a.
flipinv : {X : Type 𝓤} {p q r : X} (a : p ≡ q) (x : q ≡ r) (y : p ≡ r)
        → a ∙ x ≡ y → x ⁻¹ ≡ y ⁻¹ ∙ a
flipinv a x y H =
  ( ap (λ z → z ⁻¹ ∙ a) (H ⁻¹)
    ∙ ap (λ z → z ∙ a) (∙-inv a x)
    ∙ ∙-assoc (x ⁻¹) (a ⁻¹) a
    ∙ ap (λ z → x ⁻¹ ∙ z) (left-inv a)
    ∙ right-unit (x ⁻¹) ) ⁻¹

-- Rocq `mp_homot`: pull a path through homotopic maps.
mp-homot : {A : Type 𝓤} {B : Type 𝓥} (φ ψ : A → B)
           (h : (a : A) → φ a ≡ ψ a) {x y : A} (p : x ≡ y)
         → ap φ p ≡ h x ∙ ap ψ p ∙ (h y) ⁻¹
mp-homot φ ψ h (refl x) =
  (ap (λ z → z ∙ (h x) ⁻¹) (right-unit (h x)) ∙ right-inv (h x)) ⁻¹

------------------------------------------------------------------------
-- pentagon helpers (Rocq pentagon_mp_L / pent2 / pent_final)
------------------------------------------------------------------------

-- In our orientation `pentagonator` already matches pentagon_mp_L.
pentagon-mp-L : {A B C D E : Cat}
  (f : Map D E) (g : Map C D) (h : Map B C) (e : Map A B)
  → composeA (comp f g) h e ∙ composeA f g (comp h e)
  ≡ (ccl e (composeA f g h) ∙ composeA f (comp g h) e) ∙ ccr f (composeA g h e)
pentagon-mp-L f g h e = pentagonator f g h e

pent2 : {A B C D E : Cat}
  (f : Map D E) (g : Map C D) (h : Map B C) (e : Map A B)
  → composeA f g (comp h e) ∙ (ccr f (composeA g h e)) ⁻¹
  ≡ (composeA (comp f g) h e) ⁻¹ ∙ (ccl e (composeA f g h) ∙ composeA f (comp g h) e)
pent2 f g h e =
  slide (ccl e (composeA f g h) ∙ composeA f (comp g h) e)
        (ccr f (composeA g h e))
        (composeA (comp f g) h e)
        (composeA f g (comp h e))
        (pentagonator f g h e ⁻¹)

pent-final : {A B C D E : Cat}
  (f : Map D E) (g : Map C D) (h : Map B C) (e : Map A B)
  → composeA f (comp g h) e ∙ (ccr f (composeA g h e) ∙ (composeA f g (comp h e)) ⁻¹)
  ≡ (ccl e (composeA f g h)) ⁻¹ ∙ composeA (comp f g) h e
pent-final f g h e =
    (∙-assoc (composeA f (comp g h) e) (ccr f (composeA g h e)) ((composeA f g (comp h e)) ⁻¹)) ⁻¹
  ∙ slide (composeA (comp f g) h e)
          (composeA f g (comp h e))
          (ccl e (composeA f g h))
          (composeA f (comp g h) e ∙ ccr f (composeA g h e))
          (pentagonator f g h e
            ∙ ∙-assoc (ccl e (composeA f g h)) (composeA f (comp g h) e) (ccr f (composeA g h e)))

------------------------------------------------------------------------
-- the 3-pentagon associativity of the reassociation legs (Rocq `releg_comp`).
-- This is the isolated pentagon core; it is the only deep coherence here.
------------------------------------------------------------------------

releg-comp : {AP CP AQ CQ AR CR V : Cat}
  (v : Map CR V) (lP : Map AP CP) (lQ : Map AQ CQ) (lR : Map AR CR)
  (cg : Map CQ CR) (cf : Map CP CQ) (ag : Map AQ AR) (af : Map AP AQ)
  (slg : comp lR ag ≡ comp cg lQ) (slf : comp lQ af ≡ comp cf lP)
  → ccl lP (composeA v cg cf)
    ∙ ( composeA v (comp cg cf) lP
      ∙ ccr v ( ( (composeA lR ag af) ⁻¹ ∙ ccl af slg ∙ composeA cg lQ af
                  ∙ ccr cg slf ∙ (composeA cg cf lP) ⁻¹ ) ⁻¹ )
      ∙ (composeA v lR (comp ag af)) ⁻¹ )
  ≡ ( composeA (comp v cg) cf lP ∙ ccr (comp v cg) (slf ⁻¹)
      ∙ (composeA (comp v cg) lQ af) ⁻¹ )
    ∙ ccl af ( composeA v cg lQ ∙ ccr v (slg ⁻¹) ∙ (composeA v lR ag) ⁻¹ )
    ∙ composeA (comp v lR) ag af
releg-comp {AP} {CP} {AQ} {CQ} {AR} {CR} {V} v lP lQ lR cg cf ag af slg slf =
  mainchain ∙ Rfix ⁻¹
  where
  -- atoms
  A1 = ccl lP (composeA v cg cf)
  A2 = composeA v (comp cg cf) lP
  Z  = (composeA v lR (comp ag af)) ⁻¹
  J5 = ccr v (composeA cg cf lP)
  J4 = (ccr v (ccr cg slf)) ⁻¹
  J3 = (ccr v (composeA cg lQ af)) ⁻¹
  J2 = (ccr v (ccl af slg)) ⁻¹
  J1 = ccr v (composeA lR ag af)
  B1 = composeA (comp v cg) cf lP
  B2 = composeA v cg (comp cf lP)
  C2 = composeA v cg (comp lQ af)
  E1 = ccl af (composeA v cg lQ)
  E2 = composeA v (comp cg lQ) af
  F2 = composeA v (comp lR ag) af
  G  = composeA (comp v lR) ag af
  R1 = ccr (comp v cg) (slf ⁻¹)
  R2 = (composeA (comp v cg) lQ af) ⁻¹
  R3 = (ccl af (ccr v slg)) ⁻¹
  R4 = (ccl af (composeA v lR ag)) ⁻¹

  i1 = (composeA lR ag af) ⁻¹
  i2 = ccl af slg
  i3 = composeA cg lQ af
  i4 = ccr cg slf
  i5 = (composeA cg cf lP) ⁻¹
  INNER = ((((i1 ∙ i2) ∙ i3) ∙ i4) ∙ i5)

  NF = B1 ∙ (R1 ∙ (R2 ∙ (E1 ∙ (R3 ∙ (R4 ∙ G)))))

  -- INNER⁻¹ distribution and ccr v over it
  inv-dist : INNER ⁻¹ ≡ i5 ⁻¹ ∙ (i4 ⁻¹ ∙ (i3 ⁻¹ ∙ (i2 ⁻¹ ∙ i1 ⁻¹)))
  inv-dist =
      ∙-inv (((i1 ∙ i2) ∙ i3) ∙ i4) i5
    ∙ ap (λ z → i5 ⁻¹ ∙ z) (∙-inv ((i1 ∙ i2) ∙ i3) i4)
    ∙ ap (λ z → i5 ⁻¹ ∙ (i4 ⁻¹ ∙ z)) (∙-inv (i1 ∙ i2) i3)
    ∙ ap (λ z → i5 ⁻¹ ∙ (i4 ⁻¹ ∙ (i3 ⁻¹ ∙ z))) (∙-inv i1 i2)

  innerJ : ccr v (INNER ⁻¹) ≡ J5 ∙ (J4 ∙ (J3 ∙ (J2 ∙ J1)))
  innerJ =
      ap (λ z → ccr v z) inv-dist
    ∙ ap-∙ (comp v) (i5 ⁻¹) (i4 ⁻¹ ∙ (i3 ⁻¹ ∙ (i2 ⁻¹ ∙ i1 ⁻¹)))
    ∙ ap (λ z → ccr v (i5 ⁻¹) ∙ z) (ap-∙ (comp v) (i4 ⁻¹) (i3 ⁻¹ ∙ (i2 ⁻¹ ∙ i1 ⁻¹)))
    ∙ ap (λ z → ccr v (i5 ⁻¹) ∙ (ccr v (i4 ⁻¹) ∙ z)) (ap-∙ (comp v) (i3 ⁻¹) (i2 ⁻¹ ∙ i1 ⁻¹))
    ∙ ap (λ z → ccr v (i5 ⁻¹) ∙ (ccr v (i4 ⁻¹) ∙ (ccr v (i3 ⁻¹) ∙ z))) (ap-∙ (comp v) (i2 ⁻¹) (i1 ⁻¹))
    ∙ ∙-cong (ap (λ z → ccr v z) (⁻¹⁻¹ (composeA cg cf lP)))
        (∙-cong (ap-⁻¹ (comp v) (ccr cg slf))
          (∙-cong (ap-⁻¹ (comp v) (composeA cg lQ af))
            (∙-cong (ap-⁻¹ (comp v) (ccl af slg))
                    (ap (λ z → ccr v z) (⁻¹⁻¹ (composeA lR ag af))))))

  -- content bridges
  pentL-eq : (A1 ∙ A2) ∙ J5 ≡ B1 ∙ B2
  pentL-eq = (pentagon-mp-L v cg cf lP) ⁻¹

  cn3-eq : B2 ∙ J4 ≡ R1 ∙ C2
  cn3-eq =
      slide C2 (ccr v (ccr cg slf)) (ccr (comp v cg) slf) B2
            (compose-naturality3 v cg slf)
    ∙ ap (λ z → z ∙ C2) ((ap-⁻¹ (comp (comp v cg)) slf) ⁻¹)

  pent2-eq : C2 ∙ J3 ≡ R2 ∙ (E1 ∙ E2)
  pent2-eq = pent2 v cg lQ af

  cn2-eq : E2 ∙ J2 ≡ R3 ∙ F2
  cn2-eq =
    slide F2 (ccr v (ccl af slg)) (ccl af (ccr v slg)) E2
          (compose-naturality2 v af slg)

  pentfinal-eq : F2 ∙ (J1 ∙ Z) ≡ R4 ∙ G
  pentfinal-eq = pent-final v lR ag af

  mainchain : A1 ∙ ((A2 ∙ ccr v (INNER ⁻¹)) ∙ Z) ≡ NF
  mainchain =
      ap (λ z → A1 ∙ ((A2 ∙ z) ∙ Z)) innerJ
    ∙ solveR
        ( ι A1 ⊕ ((ι A2 ⊕ (ι J5 ⊕ (ι J4 ⊕ (ι J3 ⊕ (ι J2 ⊕ ι J1))))) ⊕ ι Z) )
        ( ((ι A1 ⊕ ι A2) ⊕ ι J5) ⊕ (ι J4 ⊕ (ι J3 ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        (refl _)
    ∙ ap (λ z → z ∙ (J4 ∙ (J3 ∙ (J2 ∙ (J1 ∙ Z))))) pentL-eq
    ∙ solveR
        ( (ι B1 ⊕ ι B2) ⊕ (ι J4 ⊕ (ι J3 ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        ( ι B1 ⊕ ((ι B2 ⊕ ι J4) ⊕ (ι J3 ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        (refl _)
    ∙ ap (λ z → B1 ∙ (z ∙ (J3 ∙ (J2 ∙ (J1 ∙ Z))))) cn3-eq
    ∙ solveR
        ( ι B1 ⊕ ((ι R1 ⊕ ι C2) ⊕ (ι J3 ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        ( ι B1 ⊕ (ι R1 ⊕ ((ι C2 ⊕ ι J3) ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        (refl _)
    ∙ ap (λ z → B1 ∙ (R1 ∙ (z ∙ (J2 ∙ (J1 ∙ Z))))) pent2-eq
    ∙ solveR
        ( ι B1 ⊕ (ι R1 ⊕ ((ι R2 ⊕ (ι E1 ⊕ ι E2)) ⊕ (ι J2 ⊕ (ι J1 ⊕ ι Z)))) )
        ( ι B1 ⊕ (ι R1 ⊕ (ι R2 ⊕ (ι E1 ⊕ ((ι E2 ⊕ ι J2) ⊕ (ι J1 ⊕ ι Z))))) )
        (refl _)
    ∙ ap (λ z → B1 ∙ (R1 ∙ (R2 ∙ (E1 ∙ (z ∙ (J1 ∙ Z)))))) cn2-eq
    ∙ solveR
        ( ι B1 ⊕ (ι R1 ⊕ (ι R2 ⊕ (ι E1 ⊕ ((ι R3 ⊕ ι F2) ⊕ (ι J1 ⊕ ι Z))))) )
        ( ι B1 ⊕ (ι R1 ⊕ (ι R2 ⊕ (ι E1 ⊕ (ι R3 ⊕ (ι F2 ⊕ (ι J1 ⊕ ι Z)))))) )
        (refl _)
    ∙ ap (λ z → B1 ∙ (R1 ∙ (R2 ∙ (E1 ∙ (R3 ∙ z))))) pentfinal-eq

  Rmid-dist : ccl af ((composeA v cg lQ ∙ ccr v (slg ⁻¹)) ∙ (composeA v lR ag) ⁻¹)
            ≡ E1 ∙ (R3 ∙ R4)
  Rmid-dist =
      ap-∙ (λ w → comp w af) (composeA v cg lQ ∙ ccr v (slg ⁻¹)) ((composeA v lR ag) ⁻¹)
    ∙ ap (λ z → z ∙ ccl af ((composeA v lR ag) ⁻¹))
         (ap-∙ (λ w → comp w af) (composeA v cg lQ) (ccr v (slg ⁻¹)))
    ∙ ap (λ z → (E1 ∙ z) ∙ ccl af ((composeA v lR ag) ⁻¹))
         (ap (λ z → ccl af z) (ap-⁻¹ (comp v) slg) ∙ ap-⁻¹ (λ w → comp w af) (ccr v slg))
    ∙ ap (λ z → (E1 ∙ R3) ∙ z) (ap-⁻¹ (λ w → comp w af) (composeA v lR ag))
    ∙ ∙-assoc E1 R3 R4

  Rfix : ((((B1 ∙ R1) ∙ R2) ∙ ccl af ((composeA v cg lQ ∙ ccr v (slg ⁻¹)) ∙ (composeA v lR ag) ⁻¹)) ∙ G)
       ≡ NF
  Rfix =
      ap (λ z → (((B1 ∙ R1) ∙ R2) ∙ z) ∙ G) Rmid-dist
    ∙ solveR
        ( (((ι B1 ⊕ ι R1) ⊕ ι R2) ⊕ (ι E1 ⊕ (ι R3 ⊕ ι R4))) ⊕ ι G )
        ( ι B1 ⊕ (ι R1 ⊕ (ι R2 ⊕ (ι E1 ⊕ (ι R3 ⊕ (ι R4 ⊕ ι G))))) )
        (refl _)

-- Rocq-oriented reB leg (SquareAlg.reB is the inverse orientation; the
-- releg-comp shape matches this one).
reBr : {P Q : Square} (m : square-morphism P Q) (X : Cat) (c : sq-cone Q X)
     → comp (comp (ce Q X c) (smB m)) (sqt P) ≡ comp (comp (ce Q X c) (sqt Q)) (smA m)
reBr {P} {Q} m X c =
    composeA (ce Q X c) (smB m) (sqt P)
  ∙ ccr (ce Q X c) ((sm-t m) ⁻¹)
  ∙ (composeA (ce Q X c) (sqt Q) (smA m)) ⁻¹

------------------------------------------------------------------------
-- the two re-leg composition laws (instances of releg-comp by conversion).
------------------------------------------------------------------------

reC-comp : {P Q R : Square} (g : square-morphism Q R) (f : square-morphism P Q)
           (X : Cat) (c : sq-cone R X)
  → ccl (sql P) (composeA (cg R X c) (smC g) (smC f)) ∙ reC (comp-sqm g f) X c
  ≡ reC f X (sq-cone-pre g X c)
    ∙ ccl (smA f) (reC g X c)
    ∙ composeA (comp (cg R X c) (sql R)) (smA g) (smA f)
reC-comp {P} {Q} {R} g f X c =
  releg-comp (cg R X c) (sql P) (sql Q) (sql R)
             (smC g) (smC f) (smA g) (smA f) (sm-l g) (sm-l f)

reB-comp : {P Q R : Square} (g : square-morphism Q R) (f : square-morphism P Q)
           (X : Cat) (c : sq-cone R X)
  → ccl (sqt P) (composeA (ce R X c) (smB g) (smB f)) ∙ reBr (comp-sqm g f) X c
  ≡ reBr f X (sq-cone-pre g X c)
    ∙ ccl (smA f) (reBr g X c)
    ∙ composeA (comp (ce R X c) (sqt R)) (smA g) (smA f)
reB-comp {P} {Q} {R} g f X c =
  releg-comp (ce R X c) (sqt P) (sqt Q) (sqt R)
             (smB g) (smB f) (smA g) (smA f) (sm-t g) (sm-t f)

------------------------------------------------------------------------
-- reB / reBr orientation conversion:  (reB m X c)⁻¹ ≡ reBr m X c.
------------------------------------------------------------------------

reB-conv : {P Q : Square} (m : square-morphism P Q) (X : Cat) (c : sq-cone Q X)
         → (reB m X c) ⁻¹ ≡ reBr m X c
reB-conv {P} {Q} m X c =
    ∙-inv (C ∙ ccr e (sm-t m)) (A ⁻¹)
  ∙ ap (λ z → z ∙ (C ∙ ccr e (sm-t m)) ⁻¹) (⁻¹⁻¹ A)
  ∙ ap (λ z → A ∙ z) (∙-inv C (ccr e (sm-t m)))
  ∙ ap (λ z → A ∙ (z ∙ C ⁻¹)) ((ap-⁻¹ (comp e) (sm-t m)) ⁻¹)
  ∙ (∙-assoc A (ccr e ((sm-t m) ⁻¹)) (C ⁻¹)) ⁻¹
  where
  e = ce Q X c
  A = composeA e (smB m) (sqt P)
  C = composeA e (sqt Q) (smA m)

------------------------------------------------------------------------
-- reB-rel: solve reB-comp for reB(comp-sqm g f) (SquareAlg orientation).
--   reB(gf) ≡ (cB⁻¹ ∙ (ccl(smA f)(reB g) ∙ reB f cg')) ∙ pe'
------------------------------------------------------------------------

reB-rel : {P Q R : Square} (g : square-morphism Q R) (f : square-morphism P Q)
          (X : Cat) (c : sq-cone R X)
        → reB (comp-sqm g f) X c
        ≡ ( (composeA (comp (ce R X c) (sqt R)) (smA g) (smA f)) ⁻¹
            ∙ (ccl (smA f) (reB g X c) ∙ reB f X (sq-cone-pre g X c)) )
          ∙ ccl (sqt P) (composeA (ce R X c) (smB g) (smB f))
reB-rel {P} {Q} {R} g f X c =
    (right-unit RBgf) ⁻¹
  ∙ ap (λ z → RBgf ∙ z) ((left-inv pe') ⁻¹)
  ∙ (∙-assoc RBgf (pe' ⁻¹) pe') ⁻¹
  ∙ ap (λ z → z ∙ pe') mid
  where
  ceR = ce R X c
  cg' = sq-cone-pre g X c
  pe' = ccl (sqt P) (composeA ceR (smB g) (smB f))
  cB  = composeA (comp ceR (sqt R)) (smA g) (smA f)
  RBgf = reB (comp-sqm g f) X c
  RBf = reB f X cg'
  P3  = ccl (smA f) (reB g X c)

  rbc' : pe' ∙ (RBgf ⁻¹) ≡ ((RBf ⁻¹) ∙ (P3 ⁻¹)) ∙ cB
  rbc' =
      ap (λ z → pe' ∙ z) (reB-conv (comp-sqm g f) X c)
    ∙ reB-comp g f X c
    ∙ ap (λ z → z ∙ cB)
         (∙-cong ((reB-conv f X cg') ⁻¹)
                 ( ap (ccl (smA f)) ((reB-conv g X c) ⁻¹)
                   ∙ ap-⁻¹ (λ w → comp w (smA f)) (reB g X c) ))

  mid : RBgf ∙ (pe' ⁻¹) ≡ (cB ⁻¹) ∙ (P3 ∙ RBf)
  mid =
      ( ∙-inv pe' (RBgf ⁻¹) ∙ ap (λ z → z ∙ pe' ⁻¹) (⁻¹⁻¹ RBgf) ) ⁻¹
    ∙ ap (λ z → z ⁻¹) rbc'
    ∙ ∙-inv ((RBf ⁻¹) ∙ (P3 ⁻¹)) cB
    ∙ ap (λ z → cB ⁻¹ ∙ z) (∙-inv (RBf ⁻¹) (P3 ⁻¹))
    ∙ ap (λ z → cB ⁻¹ ∙ z) (∙-cong (⁻¹⁻¹ P3) (⁻¹⁻¹ RBf))

------------------------------------------------------------------------
-- the composition law itself.
------------------------------------------------------------------------

sq-cone-pre-comp :
  {P Q R : Square} (g : square-morphism Q R) (f : square-morphism P Q)
  (X : Cat) (c : sq-cone R X)
  → sq-cone-pre f X (sq-cone-pre g X c) ≡ sq-cone-pre (comp-sqm g f) X c
sq-cone-pre-comp {P} {Q} {R} g f X c = cone-eq {P} {X}
    {sq-cone-pre f X (sq-cone-pre g X c)}
    {sq-cone-pre (comp-sqm g f) X c}
    pg pe coh
  where
  cgR = cg R X c
  ceR = ce R X c
  γ   = cc R X c
  cg' = sq-cone-pre g X c

  pg : cg P X (sq-cone-pre f X (sq-cone-pre g X c))
     ≡ cg P X (sq-cone-pre (comp-sqm g f) X c)
  pg = composeA cgR (smC g) (smC f)

  pe : ce P X (sq-cone-pre f X (sq-cone-pre g X c))
     ≡ ce P X (sq-cone-pre (comp-sqm g f) X c)
  pe = composeA ceR (smB g) (smB f)

  a    = ccl (sql P) pg
  pe'  = ccl (sqt P) pe
  RCgf = reC (comp-sqm g f) X c
  M    = ccl (smA (comp-sqm g f)) γ
  RBgf = reB (comp-sqm g f) X c
  RCf  = reC f X cg'
  RCg  = reC g X c
  P1   = ccl (smA f) RCg
  RBf  = reB f X cg'
  RBg  = reB g X c
  P3   = ccl (smA f) RBg
  γg   = ccl (smA g) γ
  cA   = composeA (comp cgR (sql R)) (smA g) (smA f)
  cB   = composeA (comp ceR (sqt R)) (smA g) (smA f)
  W    = (cB ⁻¹ ∙ (P3 ∙ RBf)) ∙ pe'

  NF = RCf ∙ (P1 ∙ (cA ∙ (M ∙ (cB ⁻¹ ∙ (P3 ∙ (RBf ∙ pe'))))))

  -- MM = ccl(smA f)(ccl(smA g)γ) ≡ (cA ∙ M) ∙ cB⁻¹   (ap-comp + mp-homot)
  MM-eq : ccl (smA f) γg ≡ (cA ∙ M) ∙ (cB ⁻¹)
  MM-eq =
      ap-comp (λ w → comp w (smA f)) (λ w → comp w (smA g)) γ
    ∙ mp-homot ((λ w → comp w (smA f)) ∘ (λ w → comp w (smA g)))
               (λ w → comp w (comp (smA g) (smA f)))
               (λ w → composeA w (smA g) (smA f)) γ

  -- ccl(smA f)(cc Q X cg')  ≡  (P1 ∙ MM) ∙ P3
  ccl-distrib : ccl (smA f) ((RCg ∙ γg) ∙ RBg) ≡ (P1 ∙ ccl (smA f) γg) ∙ P3
  ccl-distrib =
      ap-∙ (λ w → comp w (smA f)) (RCg ∙ γg) RBg
    ∙ ap (λ z → z ∙ P3) (ap-∙ (λ w → comp w (smA f)) RCg γg)

  coh1 : a ∙ ((RCgf ∙ M) ∙ RBgf) ≡ NF
  coh1 =
      ap (λ z → a ∙ ((RCgf ∙ M) ∙ z)) (reB-rel g f X c)
    ∙ ap (λ z → a ∙ z) (∙-assoc RCgf M W)
    ∙ (∙-assoc a RCgf (M ∙ W)) ⁻¹
    ∙ ap (λ z → z ∙ (M ∙ W)) (reC-comp g f X c)
    ∙ solveR
        ( ((ι RCf ⊕ ι P1) ⊕ ι cA) ⊕ (ι M ⊕ ((ι (cB ⁻¹) ⊕ (ι P3 ⊕ ι RBf)) ⊕ ι pe')) )
        ( ι RCf ⊕ ι P1 ⊕ ι cA ⊕ ι M ⊕ ι (cB ⁻¹) ⊕ ι P3 ⊕ ι RBf ⊕ ι pe' )
        (refl _)

  coh2 : ((RCf ∙ ccl (smA f) ((RCg ∙ γg) ∙ RBg)) ∙ RBf) ∙ pe' ≡ NF
  coh2 =
      ap (λ z → ((RCf ∙ z) ∙ RBf) ∙ pe') ccl-distrib
    ∙ ap (λ z → ((RCf ∙ ((P1 ∙ z) ∙ P3)) ∙ RBf) ∙ pe') MM-eq
    ∙ solveR
        ( ((ι RCf ⊕ ((ι P1 ⊕ ((ι cA ⊕ ι M) ⊕ ι (cB ⁻¹))) ⊕ ι P3)) ⊕ ι RBf) ⊕ ι pe' )
        ( ι RCf ⊕ ι P1 ⊕ ι cA ⊕ ι M ⊕ ι (cB ⁻¹) ⊕ ι P3 ⊕ ι RBf ⊕ ι pe' )
        (refl _)

  coh : ccl (sql P) pg ∙ cc P X (sq-cone-pre (comp-sqm g f) X c)
      ≡ cc P X (sq-cone-pre f X (sq-cone-pre g X c)) ∙ ccl (sqt P) pe
  coh = coh1 ∙ coh2 ⁻¹
