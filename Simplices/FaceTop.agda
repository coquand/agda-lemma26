{-# OPTIONS --without-K --exact-split #-}

module Simplices.FaceTop where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Interval.OrdCompare
open import Simplices.LastEdge
open import Interval.FaceOrd
open import Simplices.FaceMap
open import Foundations.SigmaEquiv

top : (n : ℕ) → Ob (Δ n)
top zero = center (terminal 𝟏c)
top (suc n) = map-to-ob (Δ n) 𝕀 (comp 𝕀₁ (! (Δ n)))

fwd-all-inr : (k : ℕ)
  → monotone-ord-fwd k ((λ _ → inr ⋆) , (λ _ _ _ → ⋆)) ≡ inr ⋆
fwd-all-inr zero = refl (inr ⋆)
fwd-all-inr (suc k) = ap (ord-suc k) (fwd-all-inr k) ∙ ord-suc-top k
  where
    ord-suc-top : (k : ℕ) → ord-suc k (inr ⋆) ≡ inr ⋆
    ord-suc-top zero = refl (inr ⋆)
    ord-suc-top (suc k) = refl (inr ⋆)

char-const-eq : (k : ℕ)
  → 𝕀-char-comparison (Δ k) (comp 𝕀₁ (! (Δ k)))
    ≡ ((λ _ → inr ⋆) , (λ _ → ⋆))
char-const-eq k =
  to-Σ-≡ (funext (λ z → const-ob-is-𝕀₁ k z) ,
           is-monotone-is-prop (λ _ → inr ⋆) _ _)

mt-const-eq : (k : ℕ)
  → pr₁ (monotone-transfer k) ((λ _ → inr ⋆) , (λ _ → ⋆))
    ≡ ((λ _ → inr ⋆) , (λ _ _ _ → ⋆))
mt-const-eq k =
  to-Σ-≡ (funext (λ o → mt-fwd-eq k ((λ _ → inr ⋆) , (λ _ → ⋆)) o) ,
           is-monotone-Ord-is-prop (λ _ → inr ⋆) _ _)

c20-top : (n : ℕ) → pr₁ (construction-20 n) (top n) ≡ ord-top n
c20-top zero = refl ⋆
c20-top (suc k) =
  ap (pr₁ (monotone-step k) ∘ 𝕀-char-comparison (Δ k))
     (ob-map-roundtrip₁ (Δ k) 𝕀 (comp 𝕀₁ (! (Δ k))))
  ∙ ap (pr₁ (monotone-step k)) (char-const-eq k)
  ∙ ap (monotone-ord-fwd k) (mt-const-eq k)
  ∙ fwd-all-inr k
