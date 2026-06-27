{-# OPTIONS --without-K --exact-split #-}

module Constructions where

open import Spartan
open import CatAxioms
open import HigherCat

------------------------------------------------------------------------
-- Extracting inverse from equivalence
------------------------------------------------------------------------

equiv-inv : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → B → A
equiv-inv (f , e) y = pr₁ (center (e y))

------------------------------------------------------------------------
-- The two objects of 𝕀
------------------------------------------------------------------------

𝕀₀ : Ob 𝕀
𝕀₀ = equiv-inv 𝕀-ob (inl ⋆)

𝕀₁ : Ob 𝕀
𝕀₁ = equiv-inv 𝕀-ob (inr ⋆)

------------------------------------------------------------------------
-- The unique map to the terminal category
------------------------------------------------------------------------

! : (A : Cat) → Map A 𝟏c
! A = center (terminal A)

------------------------------------------------------------------------
-- Domain and codomain of a morphism (Definition 10 continued)
------------------------------------------------------------------------

dom : {C : Cat} → Mor C → Ob C
dom m = comp m 𝕀₀

cod : {C : Cat} → Mor C → Ob C
cod m = comp m 𝕀₁

------------------------------------------------------------------------
-- Mapping spaces (Definition 10)
--
-- Given objects x y : Ob(C), the type of morphisms with domain x
-- and codomain y is the mapping space C(x,y).
------------------------------------------------------------------------

Hom : (C : Cat) → Ob C → Ob C → Type 𝓤₀
Hom C x y = Σ m ꞉ Mor C , (dom m ≡ x) × (cod m ≡ y)

------------------------------------------------------------------------
-- Construction 11: Identity morphisms
--
-- Given C : Cat and c : Ob(C), the identity morphism id_c is the
-- composite  𝕀 →! 𝟏c →c C.
------------------------------------------------------------------------

id-mor : {C : Cat} → Ob C → Mor C
id-mor c = comp c (! 𝕀)

-- dom(id_c) ≡ c
--
-- Proof: dom(id_c) = (c ∘ !) ∘ 𝕀₀ = c ∘ (! ∘ 𝕀₀) = c ∘ id_𝟏c = c
-- using associativity, contractibility of Map(𝟏c,𝟏c), and right unit.

dom-id : {C : Cat} (c : Ob C) → dom (id-mor c) ≡ c
dom-id c =
  (comp-assoc c (! 𝕀) 𝕀₀) ⁻¹
  ∙ ap (λ g → comp c g)
       (singletons-are-props (terminal 𝟏c) (comp (! 𝕀) 𝕀₀) (idMap 𝟏c))
  ∙ comp-id-r c

-- cod(id_c) ≡ c  (same argument with 𝕀₁)

cod-id : {C : Cat} (c : Ob C) → cod (id-mor c) ≡ c
cod-id c =
  (comp-assoc c (! 𝕀) 𝕀₁) ⁻¹
  ∙ ap (λ g → comp c g)
       (singletons-are-props (terminal 𝟏c) (comp (! 𝕀) 𝕀₁) (idMap 𝟏c))
  ∙ comp-id-r c

-- The identity morphism as an element of the mapping space C(c,c)

id-hom : {C : Cat} (c : Ob C) → Hom C c c
id-hom c = id-mor c , dom-id c , cod-id c

------------------------------------------------------------------------
-- Construction 12: The action of a functor on morphisms
--
-- Given f : A → B, postcompose a morphism 𝕀 → A with f to get
-- a morphism 𝕀 → B.
------------------------------------------------------------------------

funct-on-mor : {A B : Cat} → Map A B → Mor A → Mor B
funct-on-mor f m = comp f m

-- Naturality of domain: dom(f(m)) ≡ f(dom(m))

dom-nat : {A B : Cat} (f : Map A B) (m : Mor A)
        → dom (funct-on-mor f m) ≡ Ob-map f (dom m)
dom-nat f m = (comp-assoc f m 𝕀₀) ⁻¹

-- Naturality of codomain: cod(f(m)) ≡ f(cod(m))

cod-nat : {A B : Cat} (f : Map A B) (m : Mor A)
        → cod (funct-on-mor f m) ≡ Ob-map f (cod m)
cod-nat f m = (comp-assoc f m 𝕀₁) ⁻¹

-- The induced action on mapping spaces:
--   A(a₀, a₁) → B(f(a₀), f(a₁))

Hom-map : {A B : Cat} (f : Map A B) (a₀ a₁ : Ob A)
        → Hom A a₀ a₁ → Hom B (Ob-map f a₀) (Ob-map f a₁)
Hom-map f a₀ a₁ (m , p , q) =
  funct-on-mor f m ,
  dom-nat f m ∙ ap (Ob-map f) p ,
  cod-nat f m ∙ ap (Ob-map f) q
