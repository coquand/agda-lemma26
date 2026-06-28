{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — PUSHOUT-ALGEBRA LAYER: assembly.
--
-- Port of the Rocq `square` route (~/Desktop/LUCIE/Main.v):
--   retract of a pushout is a pushout (is_pushout_square_retract, 4655),
--   −×𝕀 preserves pushouts (times_I_preserves, 6277), and the induction
--   S_step / S_pushout (6300).  comp f g = f ∘ g throughout.
--
-- The structural algebra lives in SquareAlg; the three pentagon-heavy
-- cone lemmas in ConeUnit / ConeComp / ConeNat; −×𝕀 in TimesI.
------------------------------------------------------------------------

module Pushout where

open import Foundations.Spartan
open import Category.CatAxioms
open import Foundations.Coherence
open import Category.Constructions using (equiv-inv)
open import Category.HigherCat using (𝕀)
open import Category.Pullbacks using (_×c_; equiv-inv-rinv; equiv-inv-linv;
                            prod-comparison)
open import Category.Product using (product-map; pmc; product-map-eq1; prod-comp-equiv)
open import Posetal.Posetal using (is-posetal; posetal-hom-is-set; Delta-posetal; I-posetal)
open import Foundations.HLevels using (equiv-is-set)
open import Interval.Interval using (Δ)
open import Squares.SquareAlg
open import Squares.ConeUnit using (sq-cone-pre-id)
open import Squares.ConeComp using (sq-cone-pre-comp)
open import Squares.ConeNat  using (sq-comparison-natural)
open import Squares.TimesI   using (times-I-preserves)
open import Squares.SquareGeom using (Sq; retract-SSk)
open import Simplices.SegalGeom using (base-Sq1)

------------------------------------------------------------------------
-- §6  retract collapses to identity; the cone-level retract.
------------------------------------------------------------------------

comp-id : {S' S : Square} (R : square-retract S' S)
  (HAB : is-set (Map (sqA S') (sqB S'))) (HAC : is-set (Map (sqA S') (sqC S')))
  (HBD : is-set (Map (sqB S') (sqD S'))) (HCD : is-set (Map (sqC S') (sqD S')))
  → comp-sqm (sr-r R) (sr-s R) ≡ id-sqm S'
comp-id R HAB HAC HBD HCD =
  square-morphism-eq _ _ HAB HAC HBD HCD (sr-A R) (sr-B R) (sr-C R) (sr-D R)

sq-cone-pre-retract : {S' S : Square} (R : square-retract S' S)
  (HAB : is-set (Map (sqA S') (sqB S'))) (HAC : is-set (Map (sqA S') (sqC S')))
  (HBD : is-set (Map (sqB S') (sqD S'))) (HCD : is-set (Map (sqC S') (sqD S')))
  (X : Cat) (c : sq-cone S' X)
  → sq-cone-pre (sr-s R) X (sq-cone-pre (sr-r R) X c) ≡ c
sq-cone-pre-retract {S'} {S} R HAB HAC HBD HCD X c =
    sq-cone-pre-comp (sr-r R) (sr-s R) X c
  ∙ ap (λ m → sq-cone-pre m X c) (comp-id R HAB HAC HBD HCD)
  ∙ sq-cone-pre-id S' X c

------------------------------------------------------------------------
-- §7  RETRACT OF A PUSHOUT IS A PUSHOUT (Rocq `is_pushout_square_retract`).
------------------------------------------------------------------------

is-pushout-square-retract :
  {S' S : Square} (R : square-retract S' S)
  (HAB : is-set (Map (sqA S') (sqB S'))) (HAC : is-set (Map (sqA S') (sqC S')))
  (HBD : is-set (Map (sqB S') (sqD S'))) (HCD : is-set (Map (sqC S') (sqD S')))
  (HrD : is-set (Map (sqA S) (sqD S'))) (HsD : is-set (Map (sqA S') (sqD S)))
  → is-pushout-square S → is-pushout-square S'
is-pushout-square-retract {S'} {S} R HAB HAC HBD HCD HrD HsD HS X =
  retract-of-equiv s₀ s₁ r₀ r₁ ret₀ ret₁ (sq-comparison S' X) s₁f fr₀
  where
    e : Map (sqD S) X ≃ sq-cone S X
    e = sq-comparison S X , HS X

    s₀ : Map (sqD S') X → sq-cone S X
    s₀ h = sq-comparison S X (sq-apex-pre (sr-r R) X h)

    s₁ : sq-cone S' X → sq-cone S X
    s₁ = sq-cone-pre (sr-r R) X

    r₀ : sq-cone S X → Map (sqD S') X
    r₀ a = sq-apex-pre (sr-s R) X (equiv-inv e a)

    r₁ : sq-cone S X → sq-cone S' X
    r₁ = sq-cone-pre (sr-s R) X

    ret₀ : (h : Map (sqD S') X) → r₀ (s₀ h) ≡ h
    ret₀ h =
        ap (sq-apex-pre (sr-s R) X) (equiv-inv-linv e (sq-apex-pre (sr-r R) X h))
      ∙ composeA h (smD (sr-r R)) (smD (sr-s R))
      ∙ ccr h (sr-D R)
      ∙ comp-id-r h

    ret₁ : (c : sq-cone S' X) → r₁ (s₁ c) ≡ c
    ret₁ c = sq-cone-pre-retract R HAB HAC HBD HCD X c

    s₁f : (h : Map (sqD S') X) → s₁ (sq-comparison S' X h) ≡ s₀ h
    s₁f h = (sq-comparison-natural (sr-r R) X HrD h) ⁻¹

    fr₀ : (a : sq-cone S X) → sq-comparison S' X (r₀ a) ≡ r₁ a
    fr₀ a =
        sq-comparison-natural (sr-s R) X HsD (equiv-inv e a)
      ∙ ap (sq-cone-pre (sr-s R) X) (equiv-inv-rinv e a)

------------------------------------------------------------------------
-- §7'  ALTERNATIVE PROOF of the same statement, via the textbook
--      "retract of a MAP" lemma `retract-of-equiv-arrow` (SquareAlg §1').
--      Here the comparison map of S' is a retract of the comparison map
--      of S in the arrow category — TWO parallel maps with distinct
--      middle objects sq-cone S' X and sq-cone S X — and the pushout
--      equivalence `HS X` is supplied as g's equivalence, its inverse
--      built into f⁻¹ rather than absorbed into a single reference type.
--      The four obligations are literally the same lemmas as §7.
------------------------------------------------------------------------

is-pushout-square-retract-arrow :
  {S' S : Square} (R : square-retract S' S)
  (HAB : is-set (Map (sqA S') (sqB S'))) (HAC : is-set (Map (sqA S') (sqC S')))
  (HBD : is-set (Map (sqB S') (sqD S'))) (HCD : is-set (Map (sqC S') (sqD S')))
  (HrD : is-set (Map (sqA S) (sqD S'))) (HsD : is-set (Map (sqA S') (sqD S)))
  → is-pushout-square S → is-pushout-square S'
is-pushout-square-retract-arrow {S'} {S} R HAB HAC HBD HCD HrD HsD HS X =
  retract-of-equiv-arrow
    (sq-comparison S' X)                         -- f  : Map(D',X) → cone S'
    (sq-comparison S  X)                         -- g  : Map(D ,X) → cone S
    (sq-apex-pre (sr-r R) X)                     -- i₀ : Map(D',X) → Map(D,X)
    (sq-apex-pre (sr-s R) X)                     -- p₀ : Map(D,X)  → Map(D',X)
    (λ h → composeA h (smD (sr-r R)) (smD (sr-s R)) ∙ ccr h (sr-D R) ∙ comp-id-r h)
    (sq-cone-pre (sr-r R) X)                     -- i₁ : cone S' → cone S
    (sq-cone-pre (sr-s R) X)                     -- p₁ : cone S  → cone S'
    (sq-cone-pre-retract R HAB HAC HBD HCD X)    -- p₁ ∘ i₁ = id
    (sq-comparison-natural (sr-r R) X HrD)       -- g ∘ i₀ = i₁ ∘ f
    (sq-comparison-natural (sr-s R) X HsD)       -- f ∘ p₀ = p₁ ∘ g
    (HS X)                                       -- g is an equivalence

------------------------------------------------------------------------
-- §8  the commutation of `times-I S` from `pmc` (functoriality of
--     product-map); this is the real proof of Square's `times-I-comm`.
------------------------------------------------------------------------

times-I-comm-proof : (S : Square)
  → comp (product-map (sqr S) (idMap 𝕀)) (product-map (sqt S) (idMap 𝕀))
  ≡ comp (product-map (sqb S) (idMap 𝕀)) (product-map (sql S) (idMap 𝕀))
times-I-comm-proof S =
    (pmc (sqt S) (sqr S) (idMap 𝕀) (idMap 𝕀)) ⁻¹
  ∙ product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) (sqcomm S)
  ∙ pmc (sql S) (sqb S) (idMap 𝕀) (idMap 𝕀)

------------------------------------------------------------------------
-- §9  the input from the geometric layer (now PROVED, not postulated):
--     `Sq`, `retract-SSk` (SquareGeom), `base-Sq1` (SegalGeom), and the
--     posetalities of the corners (Delta-posetal / I-posetal, Posetal).
--     Sq n = mk-square 𝟏c (Δ 1) (Δ n) (Δ (suc n)), so each corner is a
--     simplex (or 𝕀), hence posetal; the only non-corner obligation is the
--     hom-set into the product apex sqD (times-I (Sq n)) = Δ(suc n) ×c 𝕀,
--     handled by `prod-hom-is-set` (product of two hom-sets is a set).
------------------------------------------------------------------------

-- paths in a (non-dependent) product are pairs of paths.
×-≡-η : {A : Type 𝓤} {B : Type 𝓥} {w w' : A × B} (p : w ≡ w')
      → to-×-≡ (ap pr₁ p) (ap pr₂ p) ≡ p
×-≡-η (refl _) = refl _

×-is-set : {A : Type 𝓤} {B : Type 𝓥} → is-set A → is-set B → is-set (A × B)
×-is-set sA sB w w' p q =
    (×-≡-η p) ⁻¹
  ∙ ap (λ Y → to-×-≡ (ap pr₁ p) Y) (sB (pr₂ w) (pr₂ w') (ap pr₂ p) (ap pr₂ q))
  ∙ ap (λ X → to-×-≡ X (ap pr₂ q)) (sA (pr₁ w) (pr₁ w') (ap pr₁ p) (ap pr₁ q))
  ∙ ×-≡-η q

-- the hom-set into a product apex is a set (used for the HsD hypothesis).
prod-hom-is-set : {X A B : Cat}
  → is-set (Map X A) → is-set (Map X B) → is-set (Map X (A ×c B))
prod-hom-is-set {X} {A} {B} sA sB =
  equiv-is-set (prod-comparison A B X , prod-comp-equiv A B X) (×-is-set sA sB)

------------------------------------------------------------------------
-- §10  the induction:  S(n+1) is a pushout for all n (Rocq `S_pushout`).
--      geometric-layer's `Sq` / `retract-SSk` / `base-Sq1` are used DIRECTLY — no
--      re-stated signatures, so nothing already-checked is re-normalized.
------------------------------------------------------------------------

S-step : (n : ℕ)
       → is-pushout-square (Sq (suc n))
       → is-pushout-square (Sq (suc (suc n)))
S-step n H =
  is-pushout-square-retract (retract-SSk n)
    (posetal-hom-is-set (Delta-posetal (suc zero)))
    (posetal-hom-is-set (Delta-posetal (suc (suc n))))
    (posetal-hom-is-set (Delta-posetal (suc (suc (suc n)))))
    (posetal-hom-is-set (Delta-posetal (suc (suc (suc n)))))
    (posetal-hom-is-set (Delta-posetal (suc (suc (suc n)))))
    (prod-hom-is-set (posetal-hom-is-set (Delta-posetal (suc (suc n))))
                     (posetal-hom-is-set I-posetal))
    (times-I-preserves H)

-- Base case.  `SegalGeom.base-Sq1 : is-pushout-square (Sq (suc zero))` is a real
-- proof.  With `BUILTIN NATURAL` removed, all ℕ literals are raw `suc`/`zero`
-- towers, so `base-Sq1`'s type is *syntactically* `is-pushout-square
-- (Sq (suc zero))` — α-equal to this clause's goal.  Conversion hits Agda's
-- syntactic fast path with no corner unfolding, so the (already proven) base
-- fact is used directly and type-checking stays fast.
S-pushout : (n : ℕ) → is-pushout-square (Sq (suc n))
S-pushout zero    = base-Sq1
S-pushout (suc n) = S-step n (S-pushout n)

-- Lemma 26 (square formulation): every gluing square of simplices is a pushout.
lemma26-square : (n : ℕ) → is-pushout-square (Sq (suc n))
lemma26-square = S-pushout