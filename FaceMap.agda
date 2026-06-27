{-# OPTIONS --without-K --exact-split #-}

module FaceMap where

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
open import Segal

mor-to-ord-le : (n : ℕ) (m : Mor (Δ n))
  → _≤Ord_ {n} (pr₁ (construction-20 n) (dom m))
                (pr₁ (construction-20 n) (cod m))
mor-to-ord-le zero m = ⋆
mor-to-ord-le (suc k) m =
  transport (λ a → _≤Ord_ {suc k} a (pr₁ (construction-20 (suc k)) (cod m)))
    (ap (pr₁ (construction-20 (suc k))) (px ⁻¹)
     ∙ equiv-inv-rinv (construction-20 (suc k)) x)
    (transport (λ b → _≤Ord_ {suc k} x b)
      (ap (pr₁ (construction-20 (suc k))) (py ⁻¹)
       ∙ equiv-inv-rinv (construction-20 (suc k)) y)
      le)
  where
    d  = mor-reflects-ord k m
    x  = pr₁ d
    y  = pr₁ (pr₂ d)
    px = pr₁ (pr₂ (pr₂ d))
    py = pr₁ (pr₂ (pr₂ (pr₂ d)))
    le = pr₂ (pr₂ (pr₂ (pr₂ d)))

face-p : (n : ℕ) → Ob (Δ n ×c Δ n) → 𝟚
face-p n w = face-ord n
  (pr₁ (construction-20 n) (comp (π₁ (Δ n) (Δ n)) w))
  (pr₁ (construction-20 n) (comp (π₂ (Δ n) (Δ n)) w))

face-p-mono : (n : ℕ) → is-monotone {Δ n ×c Δ n} (face-p n)
face-p-mono n m = ≤𝟚-transport pd pc
  (face-ord-mono n
    (c20 (dom m₁)) (c20 (cod m₁))
    (c20 (dom m₂)) (c20 (cod m₂))
    (mor-to-ord-le n m₁) (mor-to-ord-le n m₂))
  where
    c20 = pr₁ (construction-20 n)
    p₁  = π₁ (Δ n) (Δ n)
    p₂  = π₂ (Δ n) (Δ n)
    m₁  = comp p₁ m
    m₂  = comp p₂ m
    pd : face-ord n (c20 (dom m₁)) (c20 (dom m₂))
       ≡ face-p n (dom m)
    pd = ap (λ a → face-ord n (c20 a) (c20 (dom m₂))) (dom-nat p₁ m)
       ∙ ap (λ b → face-ord n (c20 (Ob-map p₁ (dom m))) (c20 b)) (dom-nat p₂ m)
    pc : face-ord n (c20 (cod m₁)) (c20 (cod m₂))
       ≡ face-p n (cod m)
    pc = ap (λ a → face-ord n (c20 a) (c20 (cod m₂))) (cod-nat p₁ m)
       ∙ ap (λ b → face-ord n (c20 (Ob-map p₁ (cod m))) (c20 b)) (cod-nat p₂ m)

face-adj : (n : ℕ) → Map (Δ n ×c Δ n) 𝕀
face-adj n = 𝕀-char-inverse (Δ n ×c Δ n) (face-p n , face-p-mono n)

face : (n : ℕ) → Map (Δ n) (Δ (suc n))
face n = equiv-inv (exp-equiv (Δ n) 𝕀 (Δ n)) (face-adj n)
