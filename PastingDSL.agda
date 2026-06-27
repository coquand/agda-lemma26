{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Stage 2: a tiny 2-cell pasting DSL for the wild category Cat.
--
-- Port of LUCIE `pasting.v` + the combinator block of `dsl_C.v`.
-- A `Cell f g` is a 2-cell = a path of parallel 1-cells `f ≡ g`.
-- Everything here is a renaming of the proved coherence content in
-- CatAxioms + Coherence; only `xch` (interchange) needs a proof.
--
-- Dictionary (Rocq → Agda):
--   vc = _∙_   sy = _⁻¹   idc = refl
--   lw k = ccr k  (left-whisker by k = post-compose)
--   rw h = ccl h  (right-whisker by h = pre-compose)
--   al = composeA   ul = comp-id-l   ur = comp-id-r
------------------------------------------------------------------------

module PastingDSL where

open import Spartan
open import CatAxioms
open import Coherence

private
  variable
    w x y z A B C D E : Cat

------------------------------------------------------------------------
-- 2-cells and the structural combinators
------------------------------------------------------------------------

Cell : {x y : Cat} → Map x y → Map x y → Type 𝓤₀
Cell f g = f ≡ g

infixr 6 _⊙_
_⊙_ : {f g h : Map x y} → Cell f g → Cell g h → Cell f h
_⊙_ = _∙_

vc : {f g h : Map x y} → Cell f g → Cell g h → Cell f h
vc = _∙_

sy : {f g : Map x y} → Cell f g → Cell g f
sy = _⁻¹

idc : (f : Map x y) → Cell f f
idc = refl

-- left-whisker by k  (Rocq lw / compose_congruent_right)
lw : (k : Map y z) {f g : Map x y} → Cell f g → Cell (comp k f) (comp k g)
lw k = ccr k

-- right-whisker by h  (Rocq rw / compose_congruent_left)
rw : {f g : Map y z} (h : Map x y) → Cell f g → Cell (comp f h) (comp g h)
rw h = ccl h

------------------------------------------------------------------------
-- Generator faces
------------------------------------------------------------------------

al : (f : Map y z) (g : Map x y) (h : Map w x)
   → Cell (comp (comp f g) h) (comp f (comp g h))
al = composeA

ul : (f : Map x y) → Cell (comp (idMap y) f) f
ul = comp-id-l

ur : (f : Map x y) → Cell (comp f (idMap x)) f
ur = comp-id-r

------------------------------------------------------------------------
-- The laws = the legal moves
------------------------------------------------------------------------

-- whisker is functorial in the 2-cell
lw-vc : (k : Map y z) {f g h : Map x y} (p : Cell f g) (q : Cell g h)
      → lw k (p ⊙ q) ≡ lw k p ⊙ lw k q
lw-vc k = ap-∙ (λ m → comp k m)

rw-vc : {f g h : Map y z} (e : Map x y) (p : Cell f g) (q : Cell g h)
      → rw e (p ⊙ q) ≡ rw e p ⊙ rw e q
rw-vc e = ap-∙ (λ m → comp m e)

lw-sy : (k : Map y z) {f g : Map x y} (p : Cell f g)
      → lw k (sy p) ≡ sy (lw k p)
lw-sy k = ap-⁻¹ (λ m → comp k m)

rw-sy : {f g : Map y z} (e : Map x y) (p : Cell f g)
      → rw e (sy p) ≡ sy (rw e p)
rw-sy e = ap-⁻¹ (λ m → comp m e)

-- the associator is natural in each slot (the exchange faces)
nat1 : {f f' : Map C D} (g : Map B C) (h : Map A B) (F : Cell f f')
     → al f g h ⊙ rw (comp g h) F ≡ rw h (rw g F) ⊙ al f' g h
nat1 = compose-naturality1

nat2 : (f : Map C D) {g g' : Map B C} (h : Map A B) (F : Cell g g')
     → al f g h ⊙ lw f (rw h F) ≡ rw h (lw f F) ⊙ al f g' h
nat2 = compose-naturality2

nat3 : (f : Map C D) (g : Map B C) {h h' : Map A B} (F : Cell h h')
     → al f g h ⊙ lw f (lw g F) ≡ lw (comp f g) F ⊙ al f g h'
nat3 = compose-naturality3

-- the one non-naturality face: Mac Lane's pentagon
pent : (f : Map D E) (g : Map C D) (h : Map B C) (e : Map A B)
     → al (comp f g) h e ⊙ al f g (comp h e)
     ≡ (rw e (al f g h) ⊙ al f (comp g h) e) ⊙ lw f (al g h e)
pent = pentagonator

------------------------------------------------------------------------
-- Vertical algebra of cells
------------------------------------------------------------------------

strip-l : {f g h : Map x y} (a : Cell f g) {d e : Cell g h}
        → a ⊙ d ≡ a ⊙ e → d ≡ e
strip-l = cancel-left

strip-r : {f g h : Map x y} {d e : Cell f g} (a : Cell g h)
        → d ⊙ a ≡ e ⊙ a → d ≡ e
strip-r a = cancel-right a

vassoc : {f g h i : Map x y} (p : Cell f g) (q : Cell g h) (r : Cell h i)
       → p ⊙ (q ⊙ r) ≡ (p ⊙ q) ⊙ r
vassoc p q r = (∙-assoc p q r) ⁻¹

vidr : {f g : Map x y} (p : Cell f g) → p ⊙ idc g ≡ p
vidr = right-unit

cancL : {f g h : Map x y} (a : Cell f g) (d : Cell g h) → sy a ⊙ (a ⊙ d) ≡ d
cancL (refl _) d = refl d

cancR : {f g h : Map x y} (a : Cell f g) (d : Cell f h) → a ⊙ (sy a ⊙ d) ≡ d
cancR (refl _) d = refl d

vinvL : {f g : Map x y} (a : Cell f g) → sy a ⊙ a ≡ idc g
vinvL = left-inv

vinvR : {f g : Map x y} (a : Cell f g) → a ⊙ sy a ≡ idc f
vinvR = right-inv

------------------------------------------------------------------------
-- The three unit-coherence (triangle) faces
------------------------------------------------------------------------

tri1 : (f : Map A B) (g : Map B C)
     → al (idMap C) g f ⊙ ul (comp g f) ≡ rw f (ul g)
tri1 = Id-triangle1

tri2 : (f : Map A B) (g : Map B C)
     → al g (idMap B) f ⊙ lw g (ul f) ≡ rw f (ur g)
tri2 = Id-triangle2

tri3 : (f : Map A B) (g : Map B C)
     → al g f (idMap A) ⊙ lw g (ur f) ≡ ur (comp g f)
tri3 = Id-triangle3

-- the unitors are natural
ul-nat : {f g : Map x y} (F : Cell f g) → ul f ⊙ F ≡ lw (idMap y) F ⊙ ul g
ul-nat = IdKl-nat

ur-nat : {f g : Map x y} (F : Cell f g) → ur f ⊙ F ≡ rw (idMap x) F ⊙ ur g
ur-nat = IdKr-nat

------------------------------------------------------------------------
-- Interchange (Godement): a map-cell q and an argument-cell F slide
-- past each other when whiskered.  (Rocq xch / recompose_sq.)
------------------------------------------------------------------------

xch : {m m' : Map B D} (q : Cell m m') {a b : Map A B} (F : Cell a b)
    → lw m F ⊙ rw b q ≡ rw a q ⊙ lw m' F
xch (refl m) F = right-unit (lw m F)
