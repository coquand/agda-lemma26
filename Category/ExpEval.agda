{-# OPTIONS --without-K --exact-split #-}

module Category.ExpEval where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval

exp-eval : (A B X : Cat) (h : Map (X ×c A) B) (x : Ob X)
  → ob-to-map A B (comp (equiv-inv (exp-equiv A B X) h) x)
    ≡ comp h ⟨ comp x (! A) , idMap A ⟩
exp-eval A B X h x = lhs-chain ∙ (rhs-chain) ⁻¹
  where
    u = equiv-inv (exp-equiv A B X) h
    u-rt = equiv-inv-rinv (exp-equiv A B X) h

    slice : Ob X → Map A (X ×c A)
    slice v = ⟨ comp v (! A) , idMap A ⟩

    lhs-chain :
        ob-to-map A B (comp u x)
        ≡ comp (ev A B) ⟨ comp u (comp x (! A)) , idMap A ⟩
    lhs-chain =
      (comp-assoc (ev A B)
        ⟨ comp (comp u x) (π₁ 𝟏c A) , π₂ 𝟏c A ⟩ (unit-right A)) ⁻¹
      ∙ ap (comp (ev A B))
          (pair-nat (comp (comp u x) (π₁ 𝟏c A)) (π₂ 𝟏c A) (unit-right A)
           ∙ pair-ap
               ((comp-assoc (comp u x) (π₁ 𝟏c A) (unit-right A)) ⁻¹
                ∙ ap (comp (comp u x)) (pair-β₁ (! A) (idMap A))
                ∙ (comp-assoc u x (! A)) ⁻¹)
               (pair-β₂ (! A) (idMap A)))

    rhs-chain :
        comp h (slice x)
        ≡ comp (ev A B) ⟨ comp u (comp x (! A)) , idMap A ⟩
    rhs-chain =
      ap (λ g → comp g (slice x)) (u-rt ⁻¹)
      ∙ (comp-assoc (ev A B)
          ⟨ comp u (π₁ X A) , π₂ X A ⟩ (slice x)) ⁻¹
      ∙ ap (comp (ev A B))
          (pair-nat (comp u (π₁ X A)) (π₂ X A) (slice x)
           ∙ pair-ap
               ((comp-assoc u (π₁ X A) (slice x)) ⁻¹
                ∙ ap (comp u) (pair-β₁ (comp x (! A)) (idMap A)))
               (pair-β₂ (comp x (! A)) (idMap A)))
