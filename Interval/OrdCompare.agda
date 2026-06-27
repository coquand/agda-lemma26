{-# OPTIONS --without-K --exact-split #-}

module Interval.OrdCompare where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval

ord-leq : {n : ℕ} → Ord n → Ord n → 𝟚
ord-leq {zero}  ⋆       ⋆       = inr ⋆
ord-leq {suc n} (inl x) (inl y) = ord-leq x y
ord-leq {suc n} (inl x) (inr ⋆) = inr ⋆
ord-leq {suc n} (inr ⋆) (inl y) = inl ⋆
ord-leq {suc n} (inr ⋆) (inr ⋆) = inr ⋆

ord-leq-refl : {n : ℕ} (x : Ord n) → ord-leq x x ≡ inr ⋆
ord-leq-refl {zero}  ⋆       = refl (inr ⋆)
ord-leq-refl {suc n} (inl x) = ord-leq-refl x
ord-leq-refl {suc n} (inr ⋆) = refl (inr ⋆)

ord-leq-mono : {n : ℕ} (x y : Ord n) → ord-leq x y ≡ inr ⋆ → x ≤Ord y
ord-leq-mono {zero}  ⋆       ⋆       p = ⋆
ord-leq-mono {suc n} (inl x) (inl y) p = ord-leq-mono x y p
ord-leq-mono {suc n} (inl x) (inr ⋆) p = ⋆
ord-leq-mono {suc n} (inr ⋆) (inr ⋆) p = ⋆

ord-leq-complete : {n : ℕ} (x y : Ord n) → x ≤Ord y → ord-leq x y ≡ inr ⋆
ord-leq-complete {zero}  ⋆       ⋆       p = refl (inr ⋆)
ord-leq-complete {suc n} (inl x) (inl y) p = ord-leq-complete x y p
ord-leq-complete {suc n} (inl x) (inr ⋆) p = refl (inr ⋆)
ord-leq-complete {suc n} (inr ⋆) (inr ⋆) p = refl (inr ⋆)
