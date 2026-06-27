{-# OPTIONS --without-K --exact-split #-}

module CatAxioms where

open import Spartan

------------------------------------------------------------------------
-- Axiom 1: The wild category of categories
--
-- We postulate a locally small wild category Cat.
-- Objects are called categories, morphisms are called functors.
------------------------------------------------------------------------

postulate
  Cat   : Type (𝓤₀ ⁺)
  Map   : Cat → Cat → Type 𝓤₀
  comp  : {A B C : Cat} → Map B C → Map A B → Map A C
  idMap : (C : Cat) → Map C C

  comp-assoc : {A B C D : Cat}
             → (h : Map C D) (g : Map B C) (f : Map A B)
             → comp h (comp g f) ≡ comp (comp h g) f
  comp-id-l  : {A B : Cat} (f : Map A B) → comp (idMap B) f ≡ f
  comp-id-r  : {A B : Cat} (f : Map A B) → comp f (idMap A) ≡ f

------------------------------------------------------------------------
-- Genuine 2-cell structure (Map A B is NOT a set)
--
-- `comp-assoc`, `comp-id-l/r` are non-trivial 2-cells.  We name the
-- whiskering operations and the reassociator in the *Rocq* orientation
-- so the coherence postulates and the LUCIE port read identically.
--
-- CONVENTION (pinned): Agda `comp f g = f ∘ g`, and
--   comp-assoc h g f : h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
-- is the inverse of Rocq's
--   composeA f g h : (f ∘ g) ∘ h = f ∘ (g ∘ h).
-- Hence composeA f g h := (comp-assoc f g h) ⁻¹.
------------------------------------------------------------------------

-- Right-whiskering by g on a 2-cell between left factors:
--   Rocq compose_congruent_left g H : f ∘ g = f' ∘ g
ccl : {A B C : Cat} (g : Map A B) {f f' : Map B C}
    → f ≡ f' → comp f g ≡ comp f' g
ccl g H = ap (λ m → comp m g) H

-- Left-whiskering by f on a 2-cell between right factors:
--   Rocq compose_congruent_right f H : f ∘ g = f ∘ g'
ccr : {A B C : Cat} (f : Map B C) {g g' : Map A B}
    → g ≡ g' → comp f g ≡ comp f g'
ccr f H = ap (λ m → comp f m) H

-- The reassociator in Rocq orientation:
--   composeA f g h : (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
composeA : {A B C D : Cat} (f : Map C D) (g : Map B C) (h : Map A B)
         → comp (comp f g) h ≡ comp f (comp g h)
composeA f g h = (comp-assoc f g h) ⁻¹

postulate
  -- Pentagon coherence for the reassociator (Rocq `pentagonator`).
  pentagonator :
    {A B C D E : Cat}
    (f : Map D E) (g : Map C D) (h : Map B C) (e : Map A B)
    → composeA (comp f g) h e ∙ composeA f g (comp h e)
    ≡ ccl e (composeA f g h) ∙ composeA f (comp g h) e ∙ ccr f (composeA g h e)

  -- Mac Lane triangle (Rocq `Id_triangle2`), with Id = idMap.
  Id-triangle2 :
    {A B C : Cat} (f : Map A B) (g : Map B C)
    → composeA g (idMap B) f ∙ ccr g (comp-id-l f)
    ≡ ccl f (comp-id-r g)

------------------------------------------------------------------------
-- Isomorphisms in Cat
--
-- A functor f : Map C D is an isomorphism if for every X : Cat,
-- post-composition with f is an equivalence Map(X,C) ≃ Map(X,D).
-- This is the representable (Yoneda-style) characterization.
------------------------------------------------------------------------

post-comp : {C D : Cat} (f : Map C D) (X : Cat) → Map X C → Map X D
post-comp f X g = comp f g

isIso : {C D : Cat} → Map C D → Type (𝓤₀ ⁺)
isIso f = (X : Cat) → is-equiv (post-comp f X)

------------------------------------------------------------------------
-- isIso is a proposition
--
-- Since is-equiv is a proposition (Spartan.agda) and a Π-type of
-- propositions is a proposition (by funext), isIso f is a proposition.
------------------------------------------------------------------------

isIso-is-prop : {C D : Cat} (f : Map C D) → is-prop (isIso f)
isIso-is-prop f = Π-is-prop (λ X → being-equiv-is-prop (post-comp f X))

------------------------------------------------------------------------
-- Axiom 3: Univalence of Cat
--
-- For any C : Cat, the subtype of (D : Cat) × Map(C, D) consisting
-- of invertible functors is contractible.
------------------------------------------------------------------------

Equiv-from : Cat → Type (𝓤₀ ⁺)
Equiv-from C = Σ D ꞉ Cat , Σ f ꞉ Map C D , isIso f

postulate
  cat-univalence : (C : Cat) → is-contr (Equiv-from C)

------------------------------------------------------------------------
-- Axiom 4: The terminal category
--
-- A category 𝟏c such that Map(C, 𝟏c) is contractible for all C.
------------------------------------------------------------------------

postulate
  𝟏c       : Cat
  terminal : (C : Cat) → is-contr (Map C 𝟏c)

------------------------------------------------------------------------
-- Objects of a category (Definition 6)
------------------------------------------------------------------------

Ob : Cat → Type 𝓤₀
Ob C = Map 𝟏c C

------------------------------------------------------------------------
-- The action of a functor on objects (Definition 7)
------------------------------------------------------------------------

Ob-map : {A B : Cat} → Map A B → Ob A → Ob B
Ob-map f x = comp f x
