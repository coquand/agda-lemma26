{-# OPTIONS --without-K --exact-split #-}

module Segal where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Exponentials
open import Interval

------------------------------------------------------------------------
-- Part 1: The coface maps of Δ 2
--
-- The three edges of Δ 2 as morphisms (functors 𝕀 → Δ 2)
-- with endpoint identifications.
------------------------------------------------------------------------

postulate
  d₀₁ : Mor (Δ (suc (suc zero)))
  d₁₂ : Mor (Δ (suc (suc zero)))
  d₀₂ : Mor (Δ (suc (suc zero)))
  segal-comm : cod d₀₁ ≡ dom d₁₂
  d₀₂-start  : dom d₀₂ ≡ dom d₀₁
  d₀₂-end    : cod d₀₂ ≡ cod d₁₂

------------------------------------------------------------------------
-- Part 2: Composable pairs and the Segal axiom (Axiom 21)
------------------------------------------------------------------------

ComposablePair : Cat → Type 𝓤₀
ComposablePair C = Σ f ꞉ Mor C , Σ g ꞉ Mor C , cod f ≡ dom g

segal-comparison : (C : Cat) → Map (Δ (suc (suc zero))) C → ComposablePair C
segal-comparison C σ =
  comp σ d₀₁ ,
  comp σ d₁₂ ,
  cod-nat σ d₀₁ ∙ ap (Ob-map σ) segal-comm ∙ (dom-nat σ d₁₂) ⁻¹

postulate
  segal-is-equiv : (C : Cat) → is-equiv (segal-comparison C)

segal-equiv : (C : Cat) → Map (Δ (suc (suc zero))) C ≃ ComposablePair C
segal-equiv C = segal-comparison C , segal-is-equiv C

------------------------------------------------------------------------
-- Part 3: The Segal inverse and extraction lemmas
------------------------------------------------------------------------

segal-witness : {C : Cat} → ComposablePair C → Map (Δ (suc (suc zero))) C
segal-witness {C} w = equiv-inv (segal-equiv C) w

segal-roundtrip : {C : Cat} (w : ComposablePair C)
                → segal-comparison _ (segal-witness w) ≡ w
segal-roundtrip {C} w = equiv-inv-rinv (segal-equiv C) w

segal-first : {C : Cat} (w : ComposablePair C)
            → comp (segal-witness w) d₀₁ ≡ pr₁ w
segal-first w = ap pr₁ (segal-roundtrip w)

segal-second : {C : Cat} (w : ComposablePair C)
             → comp (segal-witness w) d₁₂ ≡ pr₁ (pr₂ w)
segal-second w = ap (λ x → pr₁ (pr₂ x)) (segal-roundtrip w)

------------------------------------------------------------------------
-- Part 4: Construction 22 — Composition of morphisms
------------------------------------------------------------------------

comp-mor : {C : Cat} (f g : Mor C) → cod f ≡ dom g → Mor C
comp-mor {C} f g p = comp (segal-witness (f , g , p)) d₀₂

------------------------------------------------------------------------
-- Part 5: Domain and codomain of the composite
------------------------------------------------------------------------

dom-comp-mor : {C : Cat} (f g : Mor C) (p : cod f ≡ dom g)
             → dom (comp-mor f g p) ≡ dom f
dom-comp-mor {C} f g p =
  dom-nat σ d₀₂
  ∙ ap (Ob-map σ) d₀₂-start
  ∙ (dom-nat σ d₀₁) ⁻¹
  ∙ ap dom (segal-first w)
  where
    w = (f , g , p)
    σ = segal-witness w

cod-comp-mor : {C : Cat} (f g : Mor C) (p : cod f ≡ dom g)
             → cod (comp-mor f g p) ≡ cod g
cod-comp-mor {C} f g p =
  cod-nat σ d₀₂
  ∙ ap (Ob-map σ) d₀₂-end
  ∙ (cod-nat σ d₁₂) ⁻¹
  ∙ ap cod (segal-second w)
  where
    w = (f , g , p)
    σ = segal-witness w

------------------------------------------------------------------------
-- Part 6: Hom-level composition
------------------------------------------------------------------------

comp-hom : {C : Cat} {a b c : Ob C} → Hom C a b → Hom C b c → Hom C a c
comp-hom {C} {a} {b} {c} (f , df , cf) (g , dg , cg) =
  comp-mor f g (cf ∙ dg ⁻¹) ,
  dom-comp-mor f g (cf ∙ dg ⁻¹) ∙ df ,
  cod-comp-mor f g (cf ∙ dg ⁻¹) ∙ cg

------------------------------------------------------------------------
-- Construction 23: Unit laws for composition
--
-- Identity morphisms act as two-sided units for composition.
-- For f : Mor C, the right unit id_{cod f} ∘ f = f is witnessed by
-- the composite  Δ 2 --s₀₁₁--> 𝕀 --f--> C,  and the left unit
-- f ∘ id_{dom f} = f  by  Δ 2 --s₀₀₁--> 𝕀 --f--> C.
------------------------------------------------------------------------

-- Part 7: Degeneracy maps of Δ 2
--
-- s₀₁₁ sends vertices (0,1,2) ↦ (0,1,1), collapsing the last edge.
-- s₀₀₁ sends vertices (0,1,2) ↦ (0,0,1), collapsing the first edge.
--
-- Construction: s₀₁₁ is the Segal witness for the composable pair
-- (idMap 𝕀, id-mor 𝕀₁), and s₀₀₁ for (id-mor 𝕀₀, idMap 𝕀).
-- The d₀₁ and d₁₂ equations follow from the Segal extraction lemmas.
-- The d₀₂ equations (unit laws for identity in 𝕀) are postulated.

s₀₁₁-pair : ComposablePair 𝕀
s₀₁₁-pair = idMap 𝕀 , id-mor 𝕀₁ , p
  where
    p : cod (idMap 𝕀) ≡ dom (id-mor 𝕀₁)
    p =
      cod (idMap 𝕀)    ≡⟨ comp-id-l 𝕀₁ ⟩
      𝕀₁               ≡⟨ (dom-id 𝕀₁) ⁻¹ ⟩
      dom (id-mor 𝕀₁)  ∎

s₀₁₁ : Map (Δ (suc (suc zero))) 𝕀
s₀₁₁ = segal-witness s₀₁₁-pair

s₀₁₁-d₀₁ : comp s₀₁₁ d₀₁ ≡ idMap 𝕀
s₀₁₁-d₀₁ = segal-first s₀₁₁-pair

s₀₁₁-d₁₂ : comp s₀₁₁ d₁₂ ≡ id-mor 𝕀₁
s₀₁₁-d₁₂ = segal-second s₀₁₁-pair

s₀₀₁-pair : ComposablePair 𝕀
s₀₀₁-pair = id-mor 𝕀₀ , idMap 𝕀 , p
  where
    p : cod (id-mor 𝕀₀) ≡ dom (idMap 𝕀)
    p =
      cod (id-mor 𝕀₀)  ≡⟨ cod-id 𝕀₀ ⟩
      𝕀₀               ≡⟨ (comp-id-l 𝕀₀) ⁻¹ ⟩
      dom (idMap 𝕀)    ∎

s₀₀₁ : Map (Δ (suc (suc zero))) 𝕀
s₀₀₁ = segal-witness s₀₀₁-pair

s₀₀₁-d₀₁ : comp s₀₀₁ d₀₁ ≡ id-mor 𝕀₀
s₀₀₁-d₀₁ = segal-first s₀₀₁-pair

s₀₀₁-d₁₂ : comp s₀₀₁ d₁₂ ≡ idMap 𝕀
s₀₀₁-d₁₂ = segal-second s₀₀₁-pair

-- The interval has a unique morphism from 𝕀₀ to 𝕀₁.
-- This follows from Axiom 18 (𝕀-char): functors into 𝕀 are
-- determined by their monotone object-action, and there is
-- exactly one monotone function 𝟚 → 𝟚 sending 0 ↦ 0, 1 ↦ 1.

postulate
  𝕀-hom-contr : is-contr (Hom 𝕀 𝕀₀ 𝕀₁)

-- The d₀₂ equations: the long edge of each degeneracy is idMap 𝕀.
-- Proof: both comp s₀₁₁ d₀₂ and idMap 𝕀 are morphisms from 𝕀₀
-- to 𝕀₁, and the Hom type Hom(𝕀₀, 𝕀₁) is contractible.

s₀₁₁-d₀₂ : comp s₀₁₁ d₀₂ ≡ idMap 𝕀
s₀₁₁-d₀₂ = ap pr₁ (singletons-are-props 𝕀-hom-contr h₁ h₂)
  where
    p₁ = pr₂ (pr₂ s₀₁₁-pair)
    h₁ : Hom 𝕀 𝕀₀ 𝕀₁
    h₁ = comp s₀₁₁ d₀₂ ,
      dom-comp-mor (idMap 𝕀) (id-mor 𝕀₁) p₁ ∙ comp-id-l 𝕀₀ ,
      cod-comp-mor (idMap 𝕀) (id-mor 𝕀₁) p₁ ∙ cod-id 𝕀₁
    h₂ : Hom 𝕀 𝕀₀ 𝕀₁
    h₂ = idMap 𝕀 , comp-id-l 𝕀₀ , comp-id-l 𝕀₁

s₀₀₁-d₀₂ : comp s₀₀₁ d₀₂ ≡ idMap 𝕀
s₀₀₁-d₀₂ = ap pr₁ (singletons-are-props 𝕀-hom-contr h₁ h₂)
  where
    p₁ = pr₂ (pr₂ s₀₀₁-pair)
    h₁ : Hom 𝕀 𝕀₀ 𝕀₁
    h₁ = comp s₀₀₁ d₀₂ ,
      dom-comp-mor (id-mor 𝕀₀) (idMap 𝕀) p₁ ∙ dom-id 𝕀₀ ,
      cod-comp-mor (id-mor 𝕀₀) (idMap 𝕀) p₁ ∙ comp-id-l 𝕀₁
    h₂ : Hom 𝕀 𝕀₀ 𝕀₁
    h₂ = idMap 𝕀 , comp-id-l 𝕀₀ , comp-id-l 𝕀₁

------------------------------------------------------------------------
-- Part 8: Functors preserve identity morphisms
--
-- funct-on-mor f (id-mor x) ≡ id-mor (Ob-map f x)
-- by a single application of associativity.
------------------------------------------------------------------------

funct-pres-id : {A B : Cat} (f : Map A B) (x : Ob A)
              → funct-on-mor f (id-mor x) ≡ id-mor (Ob-map f x)
funct-pres-id f x = comp-assoc f x (! 𝕀)

------------------------------------------------------------------------
-- Part 9: Right unit witness
--
-- Given f : Mor C, the 2-simplex  comp f s₀₁₁ : Map (Δ 2) C
-- has edges (f, id_{cod f}, f), witnessing  id_{cod f} ∘ f = f.
------------------------------------------------------------------------

right-unit-witness : {C : Cat} (f : Mor C) → Map (Δ (suc (suc zero))) C
right-unit-witness f = comp f s₀₁₁

right-unit-d₀₁ : {C : Cat} (f : Mor C)
               → comp (right-unit-witness f) d₀₁ ≡ f
right-unit-d₀₁ f =
  (comp-assoc f s₀₁₁ d₀₁) ⁻¹ ∙ ap (comp f) s₀₁₁-d₀₁ ∙ comp-id-r f

right-unit-d₁₂ : {C : Cat} (f : Mor C)
               → comp (right-unit-witness f) d₁₂ ≡ id-mor (cod f)
right-unit-d₁₂ f =
  (comp-assoc f s₀₁₁ d₁₂) ⁻¹ ∙ ap (comp f) s₀₁₁-d₁₂ ∙ funct-pres-id f 𝕀₁

right-unit-d₀₂ : {C : Cat} (f : Mor C)
               → comp (right-unit-witness f) d₀₂ ≡ f
right-unit-d₀₂ f =
  (comp-assoc f s₀₁₁ d₀₂) ⁻¹ ∙ ap (comp f) s₀₁₁-d₀₂ ∙ comp-id-r f

------------------------------------------------------------------------
-- Part 10: Left unit witness
--
-- Given f : Mor C, the 2-simplex  comp f s₀₀₁ : Map (Δ 2) C
-- has edges (id_{dom f}, f, f), witnessing  f ∘ id_{dom f} = f.
------------------------------------------------------------------------

left-unit-witness : {C : Cat} (f : Mor C) → Map (Δ (suc (suc zero))) C
left-unit-witness f = comp f s₀₀₁

left-unit-d₀₁ : {C : Cat} (f : Mor C)
              → comp (left-unit-witness f) d₀₁ ≡ id-mor (dom f)
left-unit-d₀₁ f =
  (comp-assoc f s₀₀₁ d₀₁) ⁻¹ ∙ ap (comp f) s₀₀₁-d₀₁ ∙ funct-pres-id f 𝕀₀

left-unit-d₁₂ : {C : Cat} (f : Mor C)
              → comp (left-unit-witness f) d₁₂ ≡ f
left-unit-d₁₂ f =
  (comp-assoc f s₀₀₁ d₁₂) ⁻¹ ∙ ap (comp f) s₀₀₁-d₁₂ ∙ comp-id-r f

left-unit-d₀₂ : {C : Cat} (f : Mor C)
              → comp (left-unit-witness f) d₀₂ ≡ f
left-unit-d₀₂ f =
  (comp-assoc f s₀₀₁ d₀₂) ⁻¹ ∙ ap (comp f) s₀₀₁-d₀₂ ∙ comp-id-r f

------------------------------------------------------------------------
-- Part 11: The Segal left inverse and composite extraction
--
-- segal-linv recovers a 2-simplex from its comparison data.
-- comp-witness-long shows the long edge of any 2-simplex σ is the
-- Segal composite of its first two edges (with the canonical
-- composability proof from segal-comparison).
------------------------------------------------------------------------

segal-linv : {C : Cat} (σ : Map (Δ (suc (suc zero))) C)
           → segal-witness (segal-comparison C σ) ≡ σ
segal-linv {C} σ = equiv-inv-linv (segal-equiv C) σ

comp-witness-long : {C : Cat} (σ : Map (Δ (suc (suc zero))) C)
  → comp-mor (comp σ d₀₁) (comp σ d₁₂)
      (pr₂ (pr₂ (segal-comparison C σ))) ≡ comp σ d₀₂
comp-witness-long {C} σ = ap (λ τ → comp τ d₀₂) (segal-linv σ)
