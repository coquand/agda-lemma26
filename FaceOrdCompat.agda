{-# OPTIONS --without-K --exact-split #-}

module FaceOrdCompat where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import FaceOrd
open import FaceMap
open import ExpEval

------------------------------------------------------------------------
-- ev-point: evaluating ob-to-map at a point equals ev applied to pair
------------------------------------------------------------------------

ev-point : (A B : Cat) (φ : Ob (Fun A B)) (a : Ob A)
  → comp (ob-to-map A B φ) a ≡ comp (ev A B) ⟨ φ , a ⟩
ev-point A B φ a =
  (comp-assoc (exp-comparison A B 𝟏c φ) (unit-right A) a) ⁻¹
  ∙ ap (comp (exp-comparison A B 𝟏c φ))
      (pair-nat (! A) (idMap A) a
       ∙ pair-ap
           (singletons-are-props (terminal 𝟏c) (comp (! A) a) (idMap 𝟏c))
           (comp-id-l a))
  ∙ (comp-assoc (ev A B) ⟨ comp φ (π₁ 𝟏c A) , π₂ 𝟏c A ⟩ ⟨ idMap 𝟏c , a ⟩) ⁻¹
  ∙ ap (comp (ev A B))
      (pair-nat (comp φ (π₁ 𝟏c A)) (π₂ 𝟏c A) ⟨ idMap 𝟏c , a ⟩
       ∙ pair-ap
           ((comp-assoc φ (π₁ 𝟏c A) ⟨ idMap 𝟏c , a ⟩) ⁻¹
            ∙ ap (comp φ) (pair-β₁ (idMap 𝟏c) a)
            ∙ comp-id-r φ)
           (pair-β₂ (idMap 𝟏c) a))

------------------------------------------------------------------------
-- face-pw-gen: face pointwise for arbitrary object u
------------------------------------------------------------------------

private
  slice-gen : (n : ℕ) → Ob (Δ n) → Map (Δ n) (Δ n ×c Δ n)
  slice-gen n u = ⟨ comp u (! (Δ n)) , idMap (Δ n) ⟩

  slice-gen-π₁ : (n : ℕ) (u z : Ob (Δ n))
    → comp (π₁ (Δ n) (Δ n)) (comp (slice-gen n u) z) ≡ u
  slice-gen-π₁ n u z =
    comp-assoc (π₁ (Δ n) (Δ n)) (slice-gen n u) z
    ∙ ap (λ g → comp g z) (pair-β₁ (comp u (! (Δ n))) (idMap (Δ n)))
    ∙ (comp-assoc u (! (Δ n)) z) ⁻¹
    ∙ ap (comp u) (singletons-are-props (terminal 𝟏c) (comp (! (Δ n)) z) (idMap 𝟏c))
    ∙ comp-id-r u

  slice-gen-π₂ : (n : ℕ) (u z : Ob (Δ n))
    → comp (π₂ (Δ n) (Δ n)) (comp (slice-gen n u) z) ≡ z
  slice-gen-π₂ n u z =
    comp-assoc (π₂ (Δ n) (Δ n)) (slice-gen n u) z
    ∙ ap (λ g → comp g z) (pair-β₂ (comp u (! (Δ n))) (idMap (Δ n)))
    ∙ comp-id-l z

face-pw-gen : (n : ℕ) (u z : Ob (Δ n))
  → ob-to-𝟚 (ob-to-map (Δ n) 𝕀 (comp (face n) u)) z
    ≡ face-ord n (pr₁ (construction-20 n) u) (pr₁ (construction-20 n) z)
face-pw-gen n u z =
  ap (λ f → ob-to-𝟚 f z) (exp-eval (Δ n) 𝕀 (Δ n) (face-adj n) u)
  ∙ ap (pr₁ 𝕀-ob) ((comp-assoc (face-adj n) (slice-gen n u) z) ⁻¹)
  ∙ 𝕀-char-ob-to-𝟚 (Δ n ×c Δ n) (face-p n , face-p-mono n) (comp (slice-gen n u) z)
  ∙ ap (λ v → face-ord n (c20 v) (c20 (comp (π₂ (Δ n) (Δ n)) (comp (slice-gen n u) z))))
      (slice-gen-π₁ n u z)
  ∙ ap (λ v → face-ord n (c20 u) (c20 v)) (slice-gen-π₂ n u z)
  where
    c20 = pr₁ (construction-20 n)

------------------------------------------------------------------------
-- c20-face-gen-u: c20 of face applied to u gives inl (c20 u)
------------------------------------------------------------------------

c20-face-gen-u : (n : ℕ) (u : Ob (Δ n))
  → pr₁ (construction-20 (suc n)) (comp (face n) u)
    ≡ inl (pr₁ (construction-20 n) u)
c20-face-gen-u n u =
  ap (monotone-ord-fwd n) mt-eq
  ∙ monotone-ord-rinv n (inl (pr₁ (construction-20 n) u))
  where
    w = 𝕀-char-comparison (Δ n)
          (ob-to-map (Δ n) 𝕀 (comp (face n) u))
    mt-eq : pr₁ (monotone-transfer n) w
            ≡ monotone-ord-bwd n (inl (pr₁ (construction-20 n) u))
    mt-eq = to-Σ-≡
      (funext (λ o →
        mt-fwd-eq n w o
        ∙ face-pw-gen n u (equiv-inv (construction-20 n) o)
        ∙ ap (face-ord n (pr₁ (construction-20 n) u))
            (equiv-inv-rinv (construction-20 n) o))
      , is-monotone-Ord-is-prop _ _ _)
