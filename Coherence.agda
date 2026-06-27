{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Stage 1: derived coherence
--
-- Lemmas that are PROVABLE by path induction (plus the right-unit law),
-- given the postulates `pentagonator` and `Id-triangle2` in CatAxioms.
-- Mirrors the Rocq `Main.v` naturality lemmas and the two extra
-- triangle identities derived from the pentagon.
------------------------------------------------------------------------

module Coherence where

open import Spartan
open import CatAxioms

------------------------------------------------------------------------
-- Path-algebra toolkit (groupoid lemmas not already in Spartan).
-- Rocq names: maponpathscomp0, maponpathsinv0, apstar,
-- pathscomp_cancel_left / _right.
------------------------------------------------------------------------

-- ap distributes over path composition.
ap-∙ : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {x y z : A}
       (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f (refl _) q = refl _

-- ap commutes with inverse.
ap-⁻¹ : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {x y : A} (p : x ≡ y)
      → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap-⁻¹ f (refl _) = refl _

-- Congruence of path composition (Rocq apstar).
∙-cong : {A : Type 𝓤} {x y z : A} {p p' : x ≡ y} {q q' : y ≡ z}
       → p ≡ p' → q ≡ q' → p ∙ q ≡ p' ∙ q'
∙-cong (refl p) (refl q) = refl (p ∙ q)

-- Left cancellation of path composition.
cancel-left : {A : Type 𝓤} {x y z : A} (p : x ≡ y) {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left (refl _) h = h

-- Right cancellation of path composition.
cancel-right : {A : Type 𝓤} {x y z : A} {p q : x ≡ y} (r : y ≡ z)
             → p ∙ r ≡ q ∙ r → p ≡ q
cancel-right {p = p} {q} (refl _) h = (right-unit p) ⁻¹ ∙ h ∙ right-unit q

------------------------------------------------------------------------
-- Naturality of the reassociator in each of its three arguments.
-- (Rocq: compose_naturality1/2/3.)  Each is `induction F; right-unit`.
------------------------------------------------------------------------

compose-naturality1 :
  {A B C D : Cat} {f f' : Map C D} (g : Map B C) (h : Map A B) (F : f ≡ f')
  → composeA f g h ∙ ccl (comp g h) F
  ≡ ccl h (ccl g F) ∙ composeA f' g h
compose-naturality1 g h (refl f) = right-unit (composeA f g h)

compose-naturality2 :
  {A B C D : Cat} (f : Map C D) {g g' : Map B C} (h : Map A B) (F : g ≡ g')
  → composeA f g h ∙ ccr f (ccl h F)
  ≡ ccl h (ccr f F) ∙ composeA f g' h
compose-naturality2 f h (refl g) = right-unit (composeA f g h)

compose-naturality3 :
  {A B C D : Cat} (f : Map C D) (g : Map B C) {h h' : Map A B} (F : h ≡ h')
  → composeA f g h ∙ ccr f (ccr g F)
  ≡ ccr (comp f g) F ∙ composeA f g h'
compose-naturality3 f g (refl h) = right-unit (composeA f g h)

------------------------------------------------------------------------
-- Naturality of the unit laws.  (Rocq: IdKl_naturality / IdKr_naturality.)
------------------------------------------------------------------------

IdKl-nat :
  {C D : Cat} {f g : Map C D} (F : f ≡ g)
  → comp-id-l f ∙ F ≡ ccr (idMap D) F ∙ comp-id-l g
IdKl-nat (refl f) = right-unit (comp-id-l f)

IdKr-nat :
  {C D : Cat} {f g : Map C D} (F : f ≡ g)
  → comp-id-r f ∙ F ≡ ccl (idMap C) F ∙ comp-id-r g
IdKr-nat (refl f) = right-unit (comp-id-r f)

------------------------------------------------------------------------
-- Cancellation of whiskering by the identity.
-- (Rocq cancel_compose_Id_right / _left.)
-- From  ccr Id F ≡ ccr Id G  (resp. ccl)  deduce  F ≡ G,
-- using the unit-law naturality squares.
------------------------------------------------------------------------

cancel-ccr-Id : {C D : Cat} {f g : Map C D} (F G : f ≡ g)
              → ccr (idMap D) F ≡ ccr (idMap D) G → F ≡ G
cancel-ccr-Id {C} {D} {f} {g} F G H =
  cancel-left (comp-id-l f)
    (IdKl-nat F ∙ ∙-cong H (refl (comp-id-l g)) ∙ (IdKl-nat G) ⁻¹)

cancel-ccl-Id : {C D : Cat} {f g : Map C D} (F G : f ≡ g)
              → ccl (idMap C) F ≡ ccl (idMap C) G → F ≡ G
cancel-ccl-Id {C} {D} {f} {g} F G H =
  cancel-left (comp-id-r f)
    (IdKr-nat F ∙ ∙-cong H (refl (comp-id-r g)) ∙ (IdKr-nat G) ⁻¹)

------------------------------------------------------------------------
-- The other two Mac Lane triangles, derived from Id-triangle2 + pentagon.
-- (Rocq: Id_triangle1 / Id_triangle3.)  Each reduces via identity-
-- whiskering cancellation to an inner pentagon goal, then closes by
-- solving the pentagon and absorbing unit cells through the two
-- Id-triangle2 instances and the reassociator naturalities.
------------------------------------------------------------------------

Id-triangle1 : {A B C : Cat} (f : Map A B) (g : Map B C)
  → composeA (idMap C) g f ∙ comp-id-l (comp g f) ≡ ccl f (comp-id-l g)
Id-triangle1 {A} {B} {C} f g = cancel-ccr-Id _ _ inner1
  where
  C0   = idMap C
  ilg  = comp-id-l g
  ilgf = comp-id-l (comp g f)
  ε    = comp-id-r C0
  a1   = composeA C0 g f
  a1'  = composeA C0 (comp C0 g) f
  ag   = composeA C0 C0 g
  b    = composeA (comp C0 C0) g f
  c    = composeA C0 C0 (comp g f)
  P    = ccl f ag

  pent : b ∙ c ≡ P ∙ a1' ∙ ccr C0 a1
  pent = pentagonator C0 C0 g f

  tri2a : c ∙ ccr C0 ilgf ≡ ccl (comp g f) ε
  tri2a = Id-triangle2 (comp g f) C0

  tri2b : ag ∙ ccr C0 ilg ≡ ccl g ε
  tri2b = Id-triangle2 g C0

  nat1 : b ∙ ccl (comp g f) ε ≡ ccl f (ccl g ε) ∙ a1
  nat1 = compose-naturality1 g f ε

  nat2 : a1' ∙ ccr C0 (ccl f ilg) ≡ ccl f (ccr C0 ilg) ∙ a1
  nat2 = compose-naturality2 C0 f ilg

  -- ccl f (ccl g ε) ≡ P ∙ ccl f (ccr C0 ilg)   (via tri2b)
  flip : ccl f (ccl g ε) ≡ P ∙ ccl f (ccr C0 ilg)
  flip = (ap (λ p → ccl f p) tri2b) ⁻¹
       ∙ ap-∙ (λ m → comp m f) ag (ccr C0 ilg)

  lhs' : (P ∙ a1') ∙ (ccr C0 a1 ∙ ccr C0 ilgf) ≡ P ∙ (ccl f (ccr C0 ilg) ∙ a1)
  lhs' = (∙-assoc (P ∙ a1') (ccr C0 a1) (ccr C0 ilgf)) ⁻¹
       ∙ ap (λ z → z ∙ ccr C0 ilgf) (pent ⁻¹)
       ∙ ∙-assoc b c (ccr C0 ilgf)
       ∙ ap (λ z → b ∙ z) tri2a
       ∙ nat1
       ∙ ap (λ z → z ∙ a1) flip
       ∙ ∙-assoc P (ccl f (ccr C0 ilg)) a1

  rhs' : (P ∙ a1') ∙ ccr C0 (ccl f ilg) ≡ P ∙ (ccl f (ccr C0 ilg) ∙ a1)
  rhs' = ∙-assoc P a1' (ccr C0 (ccl f ilg)) ∙ ap (λ z → P ∙ z) nat2

  core' : ccr C0 a1 ∙ ccr C0 ilgf ≡ ccr C0 (ccl f ilg)
  core' = cancel-left (P ∙ a1') (lhs' ∙ rhs' ⁻¹)

  inner1 : ccr C0 (a1 ∙ ilgf) ≡ ccr C0 (ccl f ilg)
  inner1 = ap-∙ (λ m → comp C0 m) a1 ilgf ∙ core'

Id-triangle3 : {A B C : Cat} (f : Map A B) (g : Map B C)
  → composeA g f (idMap A) ∙ ccr g (comp-id-r f) ≡ comp-id-r (comp g f)
Id-triangle3 {A} {B} {C} f g = cancel-ccl-Id _ _ inner3
  where
  A0   = idMap A
  irf  = comp-id-r f
  irgf = comp-id-r (comp g f)
  δ    = comp-id-l A0
  a3   = composeA g f A0
  a3'' = composeA g (comp f A0) A0
  af3  = composeA f A0 A0
  b3   = composeA (comp g f) A0 A0
  c3   = composeA g f (comp A0 A0)
  P3   = ccl A0 a3

  pent3 : b3 ∙ c3 ≡ P3 ∙ a3'' ∙ ccr g af3
  pent3 = pentagonator g f A0 A0

  tri2a3 : b3 ∙ ccr (comp g f) δ ≡ ccl A0 irgf
  tri2a3 = Id-triangle2 A0 (comp g f)

  tri2b3 : af3 ∙ ccr f δ ≡ ccl A0 irf
  tri2b3 = Id-triangle2 A0 f

  nat2inst3 : a3'' ∙ ccr g (ccl A0 irf) ≡ ccl A0 (ccr g irf) ∙ a3
  nat2inst3 = compose-naturality2 g A0 irf

  nat3inst : c3 ∙ ccr g (ccr f δ) ≡ ccr (comp g f) δ ∙ a3
  nat3inst = compose-naturality3 g f δ

  -- distribute ccr g over tri2b3
  ggstep : ccr g (ccl A0 irf) ≡ ccr g af3 ∙ ccr g (ccr f δ)
  ggstep = (ap (λ p → ccr g p) tri2b3) ⁻¹
         ∙ ap-∙ (λ m → comp g m) af3 (ccr f δ)

  T3 : (P3 ∙ ccl A0 (ccr g irf)) ∙ a3 ≡ ccl A0 irgf ∙ a3
  T3 = ∙-assoc P3 (ccl A0 (ccr g irf)) a3
     ∙ ap (λ z → P3 ∙ z) (nat2inst3 ⁻¹)
     ∙ ap (λ z → P3 ∙ (a3'' ∙ z)) ggstep
     ∙ ap (λ z → P3 ∙ z) ((∙-assoc a3'' (ccr g af3) (ccr g (ccr f δ))) ⁻¹)
     ∙ (∙-assoc P3 (a3'' ∙ ccr g af3) (ccr g (ccr f δ))) ⁻¹
     ∙ ap (λ z → z ∙ ccr g (ccr f δ)) ((∙-assoc P3 a3'' (ccr g af3)) ⁻¹)
     ∙ ap (λ z → z ∙ ccr g (ccr f δ)) (pent3 ⁻¹)
     ∙ ∙-assoc b3 c3 (ccr g (ccr f δ))
     ∙ ap (λ z → b3 ∙ z) nat3inst
     ∙ (∙-assoc b3 (ccr (comp g f) δ) a3) ⁻¹
     ∙ ap (λ z → z ∙ a3) tri2a3

  core3' : P3 ∙ ccl A0 (ccr g irf) ≡ ccl A0 irgf
  core3' = cancel-right a3 T3

  inner3 : ccl A0 (a3 ∙ ccr g irf) ≡ ccl A0 irgf
  inner3 = ap-∙ (λ m → comp m A0) a3 (ccr g irf) ∙ core3'
