{-# OPTIONS --without-K --exact-split #-}

module LastEdge where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval
open import OrdCompare

ord-top : (n : ℕ) → Ord n
ord-top zero = ⋆
ord-top (suc n) = inr ⋆

last-edge : (n : ℕ) → Mor (Δ (suc n))
last-edge n = pr₁ (ord-to-mor-fn (suc n) (inl (ord-top n)) (inr ⋆)
  (any-≤Ord-top (inl (ord-top n))))

bwd-top-const : (n : ℕ) (x : Ord n) → pr₁ (monotone-ord-bwd n (inr ⋆)) x ≡ inr ⋆
bwd-top-const zero ⋆ = refl (inr ⋆)
bwd-top-const (suc zero) (inl ⋆) = refl (inr ⋆)
bwd-top-const (suc zero) (inr ⋆) = refl (inr ⋆)
bwd-top-const (suc (suc n)) (inl x) = bwd-top-const (suc n) x
bwd-top-const (suc (suc n)) (inr ⋆) = refl (inr ⋆)

mt-bwd-top : (n : ℕ) (z : Ob (Δ n))
  → pr₁ (equiv-inv (monotone-transfer n) (monotone-ord-bwd n (inr ⋆))) z ≡ inr ⋆
mt-bwd-top zero z = refl (inr ⋆)
mt-bwd-top (suc n) z = bwd-top-const (suc n) (pr₁ (construction-20 (suc n)) z)

const-ob-is-𝕀₁ : (n : ℕ) (z : Ob (Δ n))
  → ob-to-𝟚 (comp 𝕀₁ (! (Δ n))) z ≡ inr ⋆
const-ob-is-𝕀₁ n z =
  ap (pr₁ 𝕀-ob) ((comp-assoc 𝕀₁ (! (Δ n)) z) ⁻¹
    ∙ ap (comp 𝕀₁) (singletons-are-props (terminal 𝟏c) (comp (! (Δ n)) z) (idMap 𝟏c))
    ∙ comp-id-r 𝕀₁)
  ∙ equiv-inv-rinv 𝕀-ob (inr ⋆)

monotone-pair-eq : (n : ℕ)
  → equiv-inv (monotone-transfer n) (monotone-ord-bwd n (inr ⋆))
    ≡ 𝕀-char-comparison (Δ n) (comp 𝕀₁ (! (Δ n)))
monotone-pair-eq n =
  to-Σ-≡ (funext (λ z → mt-bwd-top n z ∙ (const-ob-is-𝕀₁ n z) ⁻¹) ,
           is-monotone-is-prop (ob-to-𝟚 (comp 𝕀₁ (! (Δ n)))) _ _)

c20-inv-top : (n : ℕ) → equiv-inv (construction-20 (suc n)) (inr ⋆)
  ≡ map-to-ob (Δ n) 𝕀 (comp 𝕀₁ (! (Δ n)))
c20-inv-top n =
  ap (map-to-ob (Δ n) 𝕀)
    (ap (𝕀-char-inverse (Δ n)) (monotone-pair-eq n)
     ∙ 𝕀-char-linv (Δ n) (comp 𝕀₁ (! (Δ n))))

edge-cod : (n : ℕ) → cod (last-edge n) ≡ map-to-ob (Δ n) 𝕀 (comp 𝕀₁ (! (Δ n)))
edge-cod n = pr₂ (pr₂ (ord-to-mor-fn (suc n) (inl (ord-top n)) (inr ⋆)
  (any-≤Ord-top (inl (ord-top n))))) ∙ c20-inv-top n

dom-last-edge : (n : ℕ)
  → dom (last-edge n) ≡ equiv-inv (construction-20 (suc n)) (inl (ord-top n))
dom-last-edge n = pr₁ (pr₂ (ord-to-mor-fn (suc n) (inl (ord-top n)) (inr ⋆)
  (any-≤Ord-top (inl (ord-top n)))))
