{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — STREAM B base: the structural algebra of square morphisms
-- and cones (Rocq Main.v 4180–4540, the parts with no genuine pentagon
-- content).  The three pentagon-heavy cores live in ConeUnit / ConeComp /
-- ConeNat; the assembly lives in Pushout.  comp f g = f ∘ g.
------------------------------------------------------------------------

module Squares.SquareAlg where

open import Foundations.Spartan
open import Category.CatAxioms
open import Foundations.Coherence
open import Category.Constructions using (equiv-inv)
open import Interval.Interval using (invertible-to-equiv)
open import Squares.Square public

------------------------------------------------------------------------
-- §0  small path-algebra helpers not already in Spartan/Coherence
------------------------------------------------------------------------

⁻¹⁻¹ : {A : Type 𝓤} {x y : A} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
⁻¹⁻¹ (refl _) = refl _

∙-inv : {A : Type 𝓤} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
∙-inv (refl _) q = (right-unit (q ⁻¹)) ⁻¹

-- transport in an identity-type (Rocq `transp_path`).
transp-path : {A : Type 𝓤} {Y : Type 𝓥} (U V : A → Y) {a a' : A}
              (e : a ≡ a') (p : U a ≡ V a)
            → transport (λ x → U x ≡ V x) e p ≡ (ap U e) ⁻¹ ∙ p ∙ ap V e
transp-path U V (refl _) p = (right-unit p) ⁻¹

to-×-≡ : {A : Type 𝓤} {B : Type 𝓥} {p p' : A × B}
       → pr₁ p ≡ pr₁ p' → pr₂ p ≡ pr₂ p' → p ≡ p'
to-×-≡ {p = a , b} {a' , b'} (refl _) (refl _) = refl _

------------------------------------------------------------------------
-- §1  type-level "retract of an equivalence is an equivalence"
--     (Rocq `isweq_by_retracts`, Main.v 3113).
------------------------------------------------------------------------

retract-of-equiv :
  {A : Type 𝓤} {B₀ : Type 𝓥} {B₁ : Type 𝓦}
  (s₀ : B₀ → A) (s₁ : B₁ → A) (r₀ : A → B₀) (r₁ : A → B₁)
  (ret₀ : (b : B₀) → r₀ (s₀ b) ≡ b) (ret₁ : (b : B₁) → r₁ (s₁ b) ≡ b)
  (f : B₀ → B₁)
  (s₁f : (b : B₀) → s₁ (f b) ≡ s₀ b) (fr₀ : (a : A) → f (r₀ a) ≡ r₁ a)
  → is-equiv f
retract-of-equiv s₀ s₁ r₀ r₁ ret₀ ret₁ f s₁f fr₀ =
  invertible-to-equiv f
    ( (λ b₁ → r₀ (s₁ b₁))
    , (λ b₁ → fr₀ (s₁ b₁) ∙ ret₁ b₁)
    , (λ b₀ → ap r₀ (s₁f b₀) ∙ ret₀ b₀) )

------------------------------------------------------------------------
-- §2  cone accessors and `cone-eq` (Rocq `cone_eq`, 4209)
--     S,X explicit (sq-cone is a definition → un-inferable from a cone).
------------------------------------------------------------------------

cg : (S : Square) (X : Cat) → sq-cone S X → Map (sqC S) X
cg S X c = pr₁ (pr₁ c)

ce : (S : Square) (X : Cat) → sq-cone S X → Map (sqB S) X
ce S X c = pr₂ (pr₁ c)

cc : (S : Square) (X : Cat) (c : sq-cone S X)
   → comp (cg S X c) (sql S) ≡ comp (ce S X c) (sqt S)
cc S X c = pr₂ c

cone-eq : {S : Square} {X : Cat} {c c' : sq-cone S X}
  (pg : cg S X c ≡ cg S X c') (pe : ce S X c ≡ ce S X c')
  (coh : ccl (sql S) pg ∙ cc S X c' ≡ cc S X c ∙ ccl (sqt S) pe)
  → c ≡ c'
cone-eq {S} {X} {(g , e) , comm} {(.g , .e) , comm'} (refl _) (refl _) coh =
  ap (λ w → ((g , e) , w)) ((coh ∙ right-unit comm) ⁻¹)

------------------------------------------------------------------------
-- §3  square morphisms: identity, composition, and equality
------------------------------------------------------------------------

id-sqm : (S : Square) → square-morphism S S
id-sqm S = mk-square-morphism
  (idMap (sqA S)) (idMap (sqB S)) (idMap (sqC S)) (idMap (sqD S))
  (comp-id-r (sqt S) ∙ (comp-id-l (sqt S)) ⁻¹)
  (comp-id-r (sql S) ∙ (comp-id-l (sql S)) ⁻¹)
  (comp-id-r (sqr S) ∙ (comp-id-l (sqr S)) ⁻¹)
  (comp-id-r (sqb S) ∙ (comp-id-l (sqb S)) ⁻¹)

comp-sqm : {P Q R : Square}
         → square-morphism Q R → square-morphism P Q → square-morphism P R
comp-sqm {P} {Q} {R} g f = mk-square-morphism
  (comp (smA g) (smA f)) (comp (smB g) (smB f))
  (comp (smC g) (smC f)) (comp (smD g) (smD f))
  ( (composeA (sqt R) (smA g) (smA f)) ⁻¹ ∙ ccl (smA f) (sm-t g)
    ∙ composeA (smB g) (sqt Q) (smA f) ∙ ccr (smB g) (sm-t f)
    ∙ (composeA (smB g) (smB f) (sqt P)) ⁻¹ )
  ( (composeA (sql R) (smA g) (smA f)) ⁻¹ ∙ ccl (smA f) (sm-l g)
    ∙ composeA (smC g) (sql Q) (smA f) ∙ ccr (smC g) (sm-l f)
    ∙ (composeA (smC g) (smC f) (sql P)) ⁻¹ )
  ( (composeA (sqr R) (smB g) (smB f)) ⁻¹ ∙ ccl (smB f) (sm-r g)
    ∙ composeA (smD g) (sqr Q) (smB f) ∙ ccr (smD g) (sm-r f)
    ∙ (composeA (smD g) (smD f) (sqr P)) ⁻¹ )
  ( (composeA (sqb R) (smC g) (smC f)) ⁻¹ ∙ ccl (smC f) (sm-b g)
    ∙ composeA (smD g) (sqb Q) (smC f) ∙ ccr (smD g) (sm-b f)
    ∙ (composeA (smD g) (smD f) (sqb P)) ⁻¹ )

square-morphism-eq : {P Q : Square} (m m' : square-morphism P Q)
  (HAB : is-set (Map (sqA P) (sqB Q))) (HAC : is-set (Map (sqA P) (sqC Q)))
  (HBD : is-set (Map (sqB P) (sqD Q))) (HCD : is-set (Map (sqC P) (sqD Q)))
  → smA m ≡ smA m' → smB m ≡ smB m' → smC m ≡ smC m' → smD m ≡ smD m'
  → m ≡ m'
square-morphism-eq
  (mk-square-morphism mA mB mC mD mt ml mr mb)
  (mk-square-morphism .mA .mB .mC .mD mt' ml' mr' mb')
  HAB HAC HBD HCD (refl _) (refl _) (refl _) (refl _) =
    ap (λ z → mk-square-morphism mA mB mC mD z ml mr mb) (HAB _ _ mt mt')
  ∙ ap (λ z → mk-square-morphism mA mB mC mD mt' z mr mb) (HAC _ _ ml ml')
  ∙ ap (λ z → mk-square-morphism mA mB mC mD mt' ml' z mb) (HBD _ _ mr mr')
  ∙ ap (λ z → mk-square-morphism mA mB mC mD mt' ml' mr' z) (HCD _ _ mb mb')

------------------------------------------------------------------------
-- §4  contravariant action on apexes and cones (Rocq `sq_apex_pre`,
--     `sq_cone_pre`, `cone_pre_comm`).
------------------------------------------------------------------------

sq-apex-pre : {P Q : Square} (m : square-morphism P Q) (X : Cat)
            → Map (sqD Q) X → Map (sqD P) X
sq-apex-pre m X h = comp h (smD m)

-- reC : the C-side reassociation leg (Rocq `reC`, 4271).
reC : {P Q : Square} (m : square-morphism P Q) (X : Cat) (c : sq-cone Q X)
    → comp (comp (cg Q X c) (smC m)) (sql P) ≡ comp (comp (cg Q X c) (sql Q)) (smA m)
reC {P} {Q} m X c =
    composeA (cg Q X c) (smC m) (sql P)
  ∙ ccr (cg Q X c) ((sm-l m) ⁻¹)
  ∙ (composeA (cg Q X c) (sql Q) (smA m)) ⁻¹

-- reB : the B-side reassociation leg, oriented as Rocq's `! reB` (4271):
--   (cone_e c ∘ sq_t Q) ∘ smA m  =  (cone_e c ∘ smB m) ∘ sq_t P.
reB : {P Q : Square} (m : square-morphism P Q) (X : Cat) (c : sq-cone Q X)
    → comp (comp (ce Q X c) (sqt Q)) (smA m) ≡ comp (comp (ce Q X c) (smB m)) (sqt P)
reB {P} {Q} m X c =
    composeA (ce Q X c) (sqt Q) (smA m)
  ∙ ccr (ce Q X c) (sm-t m)
  ∙ (composeA (ce Q X c) (smB m) (sqt P)) ⁻¹

-- cone-pre-comm DEFINITIONALLY equals  reC ∙ ccl (smA m) (cc) ∙ reB
-- (Rocq `cone_pre_comm` after `cone_pre_comm_factor`).
cone-pre-comm : {P Q : Square} (m : square-morphism P Q) (X : Cat) (c : sq-cone Q X)
  → comp (comp (cg Q X c) (smC m)) (sql P) ≡ comp (comp (ce Q X c) (smB m)) (sqt P)
cone-pre-comm {P} {Q} m X c =
  reC m X c ∙ ccl (smA m) (cc Q X c) ∙ reB m X c

sq-cone-pre : {P Q : Square} (m : square-morphism P Q) (X : Cat)
            → sq-cone Q X → sq-cone P X
sq-cone-pre {P} {Q} m X c =
  (comp (cg Q X c) (smC m) , comp (ce Q X c) (smB m)) , cone-pre-comm m X c
