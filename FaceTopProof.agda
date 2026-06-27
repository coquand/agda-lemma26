{-# OPTIONS --without-K --exact-split #-}

module FaceTopProof where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import OrdCompare
open import LastEdge
open import FaceOrd
open import FaceMap
open import FaceTop
open import ExpEval
open import SigmaEquiv

slice-top : (n : ℕ) → Map (Δ n) (Δ n ×c Δ n)
slice-top n = ⟨ comp (top n) (! (Δ n)) , idMap (Δ n) ⟩

slice-top-π₁ : (n : ℕ) (z : Ob (Δ n))
  → comp (π₁ (Δ n) (Δ n)) (comp (slice-top n) z) ≡ top n
slice-top-π₁ n z =
  comp-assoc (π₁ (Δ n) (Δ n)) (slice-top n) z
  ∙ ap (λ g → comp g z) (pair-β₁ (comp (top n) (! (Δ n))) (idMap (Δ n)))
  ∙ (comp-assoc (top n) (! (Δ n)) z) ⁻¹
  ∙ ap (comp (top n)) (singletons-are-props (terminal 𝟏c) (comp (! (Δ n)) z) (idMap 𝟏c))
  ∙ comp-id-r (top n)

slice-top-π₂ : (n : ℕ) (z : Ob (Δ n))
  → comp (π₂ (Δ n) (Δ n)) (comp (slice-top n) z) ≡ z
slice-top-π₂ n z =
  comp-assoc (π₂ (Δ n) (Δ n)) (slice-top n) z
  ∙ ap (λ g → comp g z) (pair-β₂ (comp (top n) (! (Δ n))) (idMap (Δ n)))
  ∙ comp-id-l z

face-pw : (n : ℕ) (z : Ob (Δ n))
  → ob-to-𝟚 (ob-to-map (Δ n) 𝕀 (comp (face n) (top n))) z
    ≡ face-ord n (ord-top n) (pr₁ (construction-20 n) z)
face-pw n z =
  ap (λ f → ob-to-𝟚 f z) (exp-eval (Δ n) 𝕀 (Δ n) (face-adj n) (top n))
  ∙ ap (pr₁ 𝕀-ob) ((comp-assoc (face-adj n) (slice-top n) z) ⁻¹)
  ∙ 𝕀-char-ob-to-𝟚 (Δ n ×c Δ n) (face-p n , face-p-mono n) (comp (slice-top n) z)
  ∙ ap (λ v → face-ord n (c20 v) (c20 (comp (π₂ (Δ n) (Δ n)) (comp (slice-top n) z))))
      (slice-top-π₁ n z)
  ∙ ap (λ v → face-ord n (c20 (top n)) (c20 v)) (slice-top-π₂ n z)
  ∙ ap (λ v → face-ord n v (c20 z)) (c20-top n)
  where
    c20 = pr₁ (construction-20 n)

c20-face-top : (n : ℕ)
  → pr₁ (construction-20 (suc n)) (comp (face n) (top n))
    ≡ inl (ord-top n)
c20-face-top n =
  ap (monotone-ord-fwd n) mt-eq
  ∙ monotone-ord-rinv n (inl (ord-top n))
  where
    w = 𝕀-char-comparison (Δ n)
          (ob-to-map (Δ n) 𝕀 (comp (face n) (top n)))
    mt-eq : pr₁ (monotone-transfer n) w
            ≡ monotone-ord-bwd n (inl (ord-top n))
    mt-eq = to-Σ-≡
      (funext (λ o →
        mt-fwd-eq n w o
        ∙ face-pw n (equiv-inv (construction-20 n) o)
        ∙ ap (face-ord n (ord-top n))
            (equiv-inv-rinv (construction-20 n) o))
      , is-monotone-Ord-is-prop _ _ _)

face-top : (n : ℕ) → comp (face n) (top n) ≡ dom (last-edge n)
face-top n = face-top-lhs ∙ (dom-last-edge n) ⁻¹
  where
    face-top-lhs : comp (face n) (top n)
                   ≡ equiv-inv (construction-20 (suc n)) (inl (ord-top n))
    face-top-lhs =
      equiv-inj (pr₁ (construction-20 (suc n)))
        (pr₂ (construction-20 (suc n)))
        (c20-face-top n
         ∙ (equiv-inv-rinv (construction-20 (suc n)) (inl (ord-top n))) ⁻¹)
