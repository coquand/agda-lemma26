{-# OPTIONS --without-K --exact-split #-}

module Interval.Interval where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials

------------------------------------------------------------------------
-- The order on 𝟚
--
-- 𝟚 = 𝟙 + 𝟙 is a poset with inl ⋆ ≤ inr ⋆ (i.e. 0 ≤ 1).
------------------------------------------------------------------------

_≤𝟚_ : 𝟚 → 𝟚 → Type 𝓤₀
inl _ ≤𝟚 _     = 𝟙
inr _ ≤𝟚 inl _ = 𝟘
inr _ ≤𝟚 inr _ = 𝟙

------------------------------------------------------------------------
-- The object-action map  Map(C, 𝕀) → (Ob C → 𝟚)
--
-- Given f : C → 𝕀, the composite  Ob C → Ob 𝕀 → 𝟚  sends each
-- object to its image under f, enumerated via 𝕀-ob.
------------------------------------------------------------------------

ob-to-𝟚 : {C : Cat} → Map C 𝕀 → Ob C → 𝟚
ob-to-𝟚 f x = pr₁ 𝕀-ob (Ob-map f x)

------------------------------------------------------------------------
-- Monotonicity
--
-- A function p : Ob C → 𝟚 is monotone if for every morphism
-- m : 𝕀 → C, we have p(dom m) ≤ p(cod m).
------------------------------------------------------------------------

is-monotone : {C : Cat} → (Ob C → 𝟚) → Type 𝓤₀
is-monotone {C} p = (m : Mor C) → p (dom m) ≤𝟚 p (cod m)

Monotone : Cat → Type 𝓤₀
Monotone C = Σ p ꞉ (Ob C → 𝟚) , is-monotone {C} p

------------------------------------------------------------------------
-- Axiom 8 (extended): Morphisms in 𝕀 respect the 𝕀-ob enumeration
--
-- For any morphism g : 𝕀 → 𝕀, the domain is ≤ the codomain under
-- the 𝕀-ob enumeration.  This ensures 𝕀 is oriented: morphisms
-- go from 0 to 1, not from 1 to 0.
------------------------------------------------------------------------

postulate
  𝕀-mor-order : (g : Mor 𝕀) → pr₁ 𝕀-ob (dom g) ≤𝟚 pr₁ 𝕀-ob (cod g)

------------------------------------------------------------------------
-- Axiom 18: Functors into 𝕀
--
-- The comparison map sends each functor f : C → 𝕀 to its
-- object-action composed with 𝕀-ob, together with a monotonicity
-- proof derived from 𝕀-mor-order.  This comparison is an equivalence.
------------------------------------------------------------------------

𝕀-char-comparison : (C : Cat) → Map C 𝕀 → Monotone C
𝕀-char-comparison C f = ob-to-𝟚 f , λ m →
  transport (λ b → ob-to-𝟚 f (dom m) ≤𝟚 b)
    (ap (pr₁ 𝕀-ob) (cod-nat f m))
    (transport (λ a → a ≤𝟚 pr₁ 𝕀-ob (cod (comp f m)))
      (ap (pr₁ 𝕀-ob) (dom-nat f m))
      (𝕀-mor-order (comp f m)))

postulate
  𝕀-char-inverse : (C : Cat) → Monotone C → Map C 𝕀
  𝕀-char-rinv : (C : Cat) (w : Monotone C)
    → 𝕀-char-comparison C (𝕀-char-inverse C w) ≡ w
  𝕀-char-linv : (C : Cat) (f : Map C 𝕀)
    → 𝕀-char-inverse C (𝕀-char-comparison C f) ≡ f

------------------------------------------------------------------------
-- Definition 19: The simplex categories Δ n
--
-- Δ 0       = 𝟏c        (the terminal category)
-- Δ (suc n) = Fun(Δ n, 𝕀) (functors from Δ n into 𝕀)
------------------------------------------------------------------------

Δ : ℕ → Cat
Δ zero    = 𝟏c
Δ (suc n) = Fun (Δ n) 𝕀

------------------------------------------------------------------------
-- Infrastructure for Construction 20
------------------------------------------------------------------------

-- Invertible maps are equivalences (standard HoTT fact)
--
-- Given f with quasi-inverse (g, ε, η), define
--   ε' b = ε(f(g b))⁻¹ ∙ ap f (η(g b)) ∙ ε b
-- The half-adjoint coherence  ε'(f a) ≡ ap f (η a)  follows from
-- naturality of η and ε.

private
  transport-path-l' : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {b : B}
    {x y : A} (p : x ≡ y) (r : f x ≡ b)
    → transport (λ a → f a ≡ b) p r ≡ (ap f p) ⁻¹ ∙ r
  transport-path-l' f (refl _) r = refl r

  homotopy-nat-id : {A : Type 𝓤} {f : A → A}
    (H : f ∼ id) {x y : A} (p : x ≡ y)
    → H x ∙ p ≡ ap f p ∙ H y
  homotopy-nat-id H (refl _) = right-unit _

  ∙-right-cancel : {A : Type 𝓤} {x y z : A}
    (p : x ≡ y) (q : x ≡ y) (r : y ≡ z)
    → p ∙ r ≡ q ∙ r → p ≡ q
  ∙-right-cancel p q (refl _) e = (right-unit p) ⁻¹ ∙ e ∙ right-unit q

invertible-to-equiv : {A : Type 𝓤} {B : Type 𝓥} (f : A → B)
                     → invertible f → is-equiv f
invertible-to-equiv f (g , ε , η) y = (g y , ε' y) , contr
  where
    ε' : ∀ b → f (g b) ≡ b
    ε' b = (ε (f (g b))) ⁻¹ ∙ ap f (η (g b)) ∙ ε b

    η-nat-eq : ∀ a → η (g (f a)) ≡ ap (g ∘ f) (η a)
    η-nat-eq a = ∙-right-cancel _ _ (η a) (homotopy-nat-id η (η a))

    coherence : ∀ a → ε' (f a) ≡ ap f (η a)
    coherence a =
      ∙-assoc (u ⁻¹) (ap f (η (g (f a)))) (ε (f a))
      ∙ ap (λ r → u ⁻¹ ∙ r)
          (ap (λ r → r ∙ ε (f a)) step₁ ∙ (homotopy-nat-id ε v) ⁻¹)
      ∙ (∙-assoc (u ⁻¹) u v) ⁻¹
      ∙ ap (λ r → r ∙ v) (left-inv u)
      where
        u = ε (f (g (f a)))
        v = ap f (η a)
        step₁ : ap f (η (g (f a))) ≡ ap (f ∘ g) v
        step₁ = ap (ap f) (η-nat-eq a)
                ∙ ap-comp f (g ∘ f) (η a)
                ∙ (ap-comp (f ∘ g) f (η a)) ⁻¹

    contr : (w : fiber f y) → (g y , ε' y) ≡ w
    contr (x , refl _) = to-Σ-≡ (η x , fiber-eq)
      where
        fiber-eq : transport (λ z → f z ≡ f x) (η x) (ε' (f x))
                   ≡ refl (f x)
        fiber-eq = transport-path-l' f (η x) (ε' (f x))
                   ∙ ap (λ r → (ap f (η x)) ⁻¹ ∙ r) (coherence x)
                   ∙ left-inv (ap f (η x))

-- Axiom 18 assembled: Map(C, 𝕀) ≃ Monotone C

𝕀-char : (C : Cat) → Map C 𝕀 ≃ Monotone C
𝕀-char C = 𝕀-char-comparison C ,
  invertible-to-equiv (𝕀-char-comparison C)
    (𝕀-char-inverse C , 𝕀-char-rinv C , 𝕀-char-linv C)

-- Composition of equivalences

equiv-comp : {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
           → A ≃ B → B ≃ C → A ≃ C
equiv-comp e₁ e₂ =
  (λ a → pr₁ e₂ (pr₁ e₁ a)) ,
  invertible-to-equiv (λ a → pr₁ e₂ (pr₁ e₁ a))
    ((λ c → equiv-inv e₁ (equiv-inv e₂ c)) ,
     (λ c → ap (pr₁ e₂) (equiv-inv-rinv e₁ (equiv-inv e₂ c))
            ∙ equiv-inv-rinv e₂ c) ,
     (λ a → ap (equiv-inv e₁) (equiv-inv-linv e₂ (pr₁ e₁ a))
            ∙ equiv-inv-linv e₁ a))

-- Contractible types are equivalent to 𝟙

contr-equiv-𝟙 : {A : Type 𝓤₀} → is-contr A → A ≃ 𝟙
contr-equiv-𝟙 (c , φ) =
  (λ _ → ⋆) ,
  invertible-to-equiv (λ _ → ⋆)
    ((λ _ → c) ,
     𝟙-induction (λ y → ⋆ ≡ y) (refl ⋆) ,
     φ)

------------------------------------------------------------------------
-- Remark 16 (full equivalence): Ob(Fun(A,B)) ≃ Map(A,B)
--
-- Assembled from the round-trips ob-map-roundtrip₁ and
-- ob-map-roundtrip₂ proved in Exponentials.
------------------------------------------------------------------------

ob-map-equiv : (A B : Cat) → Ob (Fun A B) ≃ Map A B
ob-map-equiv A B =
  ob-to-map A B ,
  invertible-to-equiv (ob-to-map A B)
    (map-to-ob A B , ob-map-roundtrip₁ A B , ob-map-roundtrip₂ A B)

------------------------------------------------------------------------
-- Ordinal types
--
-- Ord n is a finite totally ordered type with (n + 1) elements:
--   Ord 0       = 𝟙          (1 element)
--   Ord (suc n) = Ord n + 𝟙  (n + 2 elements)
------------------------------------------------------------------------

Ord : ℕ → Type 𝓤₀
Ord zero    = 𝟙
Ord (suc n) = Ord n + 𝟙

-- The total order on Ord n

_≤Ord_ : {n : ℕ} → Ord n → Ord n → Type 𝓤₀
_≤Ord_ {zero}  _ _             = 𝟙
_≤Ord_ {suc n} (inl x) (inl y) = _≤Ord_ {n} x y
_≤Ord_ {suc n} (inl _) (inr _) = 𝟙
_≤Ord_ {suc n} (inr _) (inl _) = 𝟘
_≤Ord_ {suc n} (inr _) (inr _) = 𝟙

------------------------------------------------------------------------
-- Helper lemmas for ≤𝟚
------------------------------------------------------------------------

≤𝟚-refl : (x : 𝟚) → x ≤𝟚 x
≤𝟚-refl (inl _) = ⋆
≤𝟚-refl (inr _) = ⋆

any-≤𝟚-top : (x : 𝟚) → x ≤𝟚 inr ⋆
any-≤𝟚-top (inl _) = ⋆
any-≤𝟚-top (inr _) = ⋆

≤𝟚-inl-forces-inl : (x : 𝟚) → x ≤𝟚 inl ⋆ → x ≡ inl ⋆
≤𝟚-inl-forces-inl (inl ⋆) _ = refl (inl ⋆)
≤𝟚-inl-forces-inl (inr ⋆) ()

≤𝟚-is-prop : (x y : 𝟚) → is-prop (x ≤𝟚 y)
≤𝟚-is-prop (inl _) (inl _) = singletons-are-props (⋆ , 𝟙-induction _ (refl ⋆))
≤𝟚-is-prop (inl _) (inr _) = singletons-are-props (⋆ , 𝟙-induction _ (refl ⋆))
≤𝟚-is-prop (inr _) (inl _) = 𝟘-induction (λ x → (y : 𝟘) → x ≡ y)
≤𝟚-is-prop (inr _) (inr _) = singletons-are-props (⋆ , 𝟙-induction _ (refl ⋆))

------------------------------------------------------------------------
-- Order-theoretic monotone maps on Ord n
------------------------------------------------------------------------

is-monotone-Ord : {n : ℕ} → (Ord n → 𝟚) → Type 𝓤₀
is-monotone-Ord {n} q = (x y : Ord n) → x ≤Ord y → q x ≤𝟚 q y

MonotoneOrd : ℕ → Type 𝓤₀
MonotoneOrd n = Σ q ꞉ (Ord n → 𝟚) , is-monotone-Ord {n} q

is-monotone-Ord-is-prop : {n : ℕ} (q : Ord n → 𝟚)
                        → is-prop (is-monotone-Ord {n} q)
is-monotone-Ord-is-prop q =
  Π-is-prop (λ x → Π-is-prop (λ y →
    Π-is-prop (λ _ → ≤𝟚-is-prop (q x) (q y))))

-- Every element of Ord(suc n) is ≤ the top element
any-≤Ord-top : {n : ℕ} (z : Ord (suc n)) → _≤Ord_ {suc n} z (inr ⋆)
any-≤Ord-top (inl _) = ⋆
any-≤Ord-top (inr _) = ⋆

-- When the top value is 0, monotonicity forces the function to be
-- constantly 0
all-const-from-top : {n : ℕ} (q : Ord (suc n) → 𝟚)
  → is-monotone-Ord {suc n} q → q (inr ⋆) ≡ inl ⋆
  → (z : Ord (suc n)) → q z ≡ inl ⋆
all-const-from-top q mono p z =
  ≤𝟚-inl-forces-inl (q z)
    (transport (λ b → q z ≤𝟚 b) p (mono z (inr ⋆) (any-≤Ord-top z)))

------------------------------------------------------------------------
-- Ordinal helpers for the order-preserving bijection
------------------------------------------------------------------------

-- Ordinal successor: shifts ordinal k to k+1

ord-suc : (n : ℕ) → Ord (suc n) → Ord (suc (suc n))
ord-suc zero    (inl ⋆) = inl (inr ⋆)
ord-suc zero    (inr ⋆) = inr ⋆
ord-suc (suc n) (inl x) = inl (ord-suc n x)
ord-suc (suc n) (inr ⋆) = inr ⋆

-- Classify ordinal as bottom or successor of another

ord-unsuc-lift : (n : ℕ) → 𝟙 + Ord (suc n) → 𝟙 + Ord (suc (suc n))
ord-unsuc-lift n (inl ⋆) = inl ⋆
ord-unsuc-lift n (inr c) = inr (inl c)

ord-unsuc : (n : ℕ) → Ord (suc (suc n)) → 𝟙 + Ord (suc n)
ord-unsuc zero    (inl (inl ⋆)) = inl ⋆
ord-unsuc zero    (inl (inr ⋆)) = inr (inl ⋆)
ord-unsuc zero    (inr ⋆)       = inr (inr ⋆)
ord-unsuc (suc n) (inl (inl y)) = ord-unsuc-lift n (ord-unsuc n (inl y))
ord-unsuc (suc n) (inl (inr ⋆)) = inr (inl (inr ⋆))
ord-unsuc (suc n) (inr ⋆)       = inr (inr ⋆)

-- Key lemma: ord-unsuc is a left inverse of ord-suc

ord-unsuc-suc : (n : ℕ) (c : Ord (suc n))
              → ord-unsuc n (ord-suc n c) ≡ inr c
ord-unsuc-suc zero    (inl ⋆) = refl _
ord-unsuc-suc zero    (inr ⋆) = refl _
ord-unsuc-suc (suc n) (inr ⋆) = refl _
ord-unsuc-suc (suc zero)    (inl (inl ⋆)) = refl _
ord-unsuc-suc (suc zero)    (inl (inr ⋆)) = refl _
ord-unsuc-suc (suc (suc n)) (inl (inl y)) =
  ap (ord-unsuc-lift (suc n)) (ord-unsuc-suc (suc n) (inl y))
ord-unsuc-suc (suc (suc n)) (inl (inr ⋆)) = refl _

-- Bottom ordinal of Ord (suc n)

ord-bot : (n : ℕ) → Ord (suc n)
ord-bot zero    = inl ⋆
ord-bot (suc n) = inl (ord-bot n)

-- Reconstruct an ordinal from its classification

ord-from-class : (n : ℕ) → 𝟙 + Ord (suc n) → Ord (suc (suc n))
ord-from-class n (inl ⋆)  = inl (ord-bot n)
ord-from-class n (inr c') = ord-suc n c'

-- ord-from-class is a right inverse of ord-unsuc

ord-class-rinv : (n : ℕ) (c : Ord (suc (suc n)))
               → ord-from-class n (ord-unsuc n c) ≡ c

ord-class-rinv-step
  : (n : ℕ) (y : Ord (suc n)) (r : 𝟙 + Ord (suc n))
  → ord-unsuc n (inl y) ≡ r → ord-from-class n r ≡ inl y
  → ord-from-class (suc n) (ord-unsuc-lift n r) ≡ inl (inl y)
ord-class-rinv-step n y (inl ⋆) eq ih = ap inl ih
ord-class-rinv-step n y (inr c'') eq ih = ap inl ih

ord-class-rinv zero (inl (inl ⋆)) = refl _
ord-class-rinv zero (inl (inr ⋆)) = refl _
ord-class-rinv zero (inr ⋆)       = refl _
ord-class-rinv (suc zero)    (inl (inr ⋆)) = refl _
ord-class-rinv (suc (suc n)) (inl (inr ⋆)) = refl _
ord-class-rinv (suc zero)    (inr ⋆)  = refl _
ord-class-rinv (suc (suc n)) (inr ⋆) = refl _
ord-class-rinv (suc n) (inl (inl y)) =
  ord-class-rinv-step n y (ord-unsuc n (inl y)) (refl _) (ord-class-rinv n (inl y))

-- ord-unsuc maps the bottom ordinal to inl ⋆

ord-unsuc-bot : (n : ℕ) → ord-unsuc n (inl (ord-bot n)) ≡ inl ⋆
ord-unsuc-bot zero    = refl _
ord-unsuc-bot (suc n) = ap (ord-unsuc-lift n) (ord-unsuc-bot n)

------------------------------------------------------------------------
-- The combinatorial equivalence: MonotoneOrd n ≃ Ord(suc n)
--
-- Order-preserving bijection: the all-zeros function maps to the
-- bottom ordinal, and functions with top=1 are shifted up by 1.
------------------------------------------------------------------------

-- Forward and backward maps (mutually recursive with helper)

monotone-ord-fwd-suc : (n : ℕ) → 𝟚 → MonotoneOrd n → Ord (suc (suc n))
monotone-ord-fwd     : (n : ℕ) → MonotoneOrd n → Ord (suc n)

monotone-ord-fwd-suc n (inl _) w₀ = inl (monotone-ord-fwd n w₀)
monotone-ord-fwd-suc n (inr _) w₀ = ord-suc n (monotone-ord-fwd n w₀)

monotone-ord-fwd zero (q , _) = q ⋆
monotone-ord-fwd (suc n) (q , mono) =
  monotone-ord-fwd-suc n (q (inr ⋆))
    ((λ x → q (inl x)) , (λ x y le → mono (inl x) (inl y) le))

-- Helper for backward map: takes the classification result

monotone-ord-bwd : (n : ℕ) → Ord (suc n) → MonotoneOrd n
monotone-ord-bwd-aux : (n : ℕ) → 𝟙 + Ord (suc n) → MonotoneOrd (suc n)
monotone-ord-bwd-aux n (inl ⋆) = (λ _ → inl ⋆) , (λ _ _ _ → ⋆)
monotone-ord-bwd-aux n (inr c') = q , mono
  where
    rec = monotone-ord-bwd n c'
    q : Ord (suc n) → 𝟚
    q (inl x) = pr₁ rec x
    q (inr _) = inr ⋆
    mono : is-monotone-Ord {suc n} q
    mono (inl x) (inl y) le = pr₂ rec x y le
    mono (inl x) (inr _) _  = any-≤𝟚-top (pr₁ rec x)
    mono (inr _) (inl _) ()
    mono (inr _) (inr _) _  = ⋆

monotone-ord-bwd zero b = (λ _ → b) , (λ _ _ _ → ≤𝟚-refl b)
monotone-ord-bwd (suc n) c = monotone-ord-bwd-aux n (ord-unsuc n c)

-- fwd of the all-zeros function is the bottom ordinal

fwd-all-zeros : (n : ℕ)
  → monotone-ord-fwd n ((λ _ → inl ⋆) , (λ _ _ _ → ⋆)) ≡ ord-bot n
fwd-all-zeros zero    = refl _
fwd-all-zeros (suc n) = ap inl (fwd-all-zeros n)

-- Round-trip 1: fwd ∘ bwd ∼ id

monotone-ord-rinv : (n : ℕ) (c : Ord (suc n))
                  → monotone-ord-fwd n (monotone-ord-bwd n c) ≡ c

monotone-ord-rinv-aux
  : (n : ℕ) (c : Ord (suc (suc n))) (r : 𝟙 + Ord (suc n))
  → ord-unsuc n c ≡ r
  → monotone-ord-fwd (suc n) (monotone-ord-bwd-aux n r) ≡ c

monotone-ord-rinv-aux n c (inl ⋆) p =
  ap inl (fwd-all-zeros n)
  ∙ ((ap (ord-from-class n) p) ⁻¹ ∙ ord-class-rinv n c)
monotone-ord-rinv-aux n c (inr c') p =
  ap (ord-suc n) (monotone-ord-rinv n c')
  ∙ ((ap (ord-from-class n) p) ⁻¹ ∙ ord-class-rinv n c)

monotone-ord-rinv zero c = refl c
monotone-ord-rinv (suc n) c =
  monotone-ord-rinv-aux n c (ord-unsuc n c) (refl _)

-- Round-trip 2: bwd ∘ fwd ∼ id

monotone-ord-linv : (n : ℕ) (w : MonotoneOrd n)
                  → monotone-ord-bwd n (monotone-ord-fwd n w) ≡ w

monotone-ord-linv-suc
  : (n : ℕ) (q : Ord (suc n) → 𝟚) (mono : is-monotone-Ord {suc n} q)
  → (b : 𝟚) → q (inr ⋆) ≡ b
  → monotone-ord-bwd (suc n)
      (monotone-ord-fwd-suc n b
        ((λ x → q (inl x)) , (λ x y le → mono (inl x) (inl y) le)))
    ≡ (q , mono)

monotone-ord-linv-suc n q mono (inl ⋆) p =
  lhs-step ∙ rhs-step ⁻¹
  where
    w₀ = ((λ x → q (inl x)) , (λ x y le → mono (inl x) (inl y) le))
    az : MonotoneOrd n
    az = ((λ _ → inl ⋆) , (λ _ _ _ → ⋆))
    w₀-eq : w₀ ≡ az
    w₀-eq = to-Σ-≡ (funext (λ x → all-const-from-top q mono p (inl x)) ,
                     is-monotone-Ord-is-prop (λ _ → inl ⋆) _ _)
    lhs-step : monotone-ord-bwd-aux n (ord-unsuc n (inl (monotone-ord-fwd n w₀)))
             ≡ ((λ _ → inl ⋆) , (λ _ _ _ → ⋆))
    lhs-step =
      ap (λ v → monotone-ord-bwd-aux n (ord-unsuc n (inl (monotone-ord-fwd n v)))) w₀-eq
      ∙ ap (λ c → monotone-ord-bwd-aux n (ord-unsuc n (inl c))) (fwd-all-zeros n)
      ∙ ap (monotone-ord-bwd-aux n) (ord-unsuc-bot n)
    rhs-step : (q , mono) ≡ ((λ _ → inl ⋆) , (λ _ _ _ → ⋆))
    rhs-step = to-Σ-≡ (funext (λ z → all-const-from-top q mono p z) ,
                        is-monotone-Ord-is-prop (λ _ → inl ⋆) _ _)
monotone-ord-linv-suc n q mono (inr ⋆) p =
  ap (monotone-ord-bwd-aux n) (ord-unsuc-suc n (monotone-ord-fwd n w₀))
  ∙ step₂
  where
    w₀ = ((λ x → q (inl x)) , (λ x y le → mono (inl x) (inl y) le))
    step₂ : monotone-ord-bwd-aux n (inr (monotone-ord-fwd n w₀)) ≡ (q , mono)
    step₂ = to-Σ-≡ (funext fun-eq , is-monotone-Ord-is-prop q _ mono)
      where
        fun-eq : (z : Ord (suc n))
          → pr₁ (monotone-ord-bwd-aux n (inr (monotone-ord-fwd n w₀))) z ≡ q z
        fun-eq (inl x) = ap (λ w → pr₁ w x) (monotone-ord-linv n w₀)
        fun-eq (inr ⋆) = p ⁻¹

monotone-ord-linv zero (q , mono) =
  to-Σ-≡ (funext (𝟙-induction (λ x → q ⋆ ≡ q x) (refl (q ⋆))) ,
           is-monotone-Ord-is-prop q _ mono)
monotone-ord-linv (suc n) (q , mono) =
  monotone-ord-linv-suc n q mono (q (inr ⋆)) (refl (q (inr ⋆)))

-- The combinatorial equivalence

monotone-ord : (n : ℕ) → MonotoneOrd n ≃ Ord (suc n)
monotone-ord n = monotone-ord-fwd n ,
  invertible-to-equiv (monotone-ord-fwd n)
    (monotone-ord-bwd n , monotone-ord-rinv n , monotone-ord-linv n)

------------------------------------------------------------------------
-- Ordinal ordering helpers
------------------------------------------------------------------------

-- The bottom ordinal is ≤ everything

ord-bot-le : (n : ℕ) (y : Ord (suc n)) → _≤Ord_ {suc n} (ord-bot n) y
ord-bot-le zero (inl _) = ⋆
ord-bot-le zero (inr _) = ⋆
ord-bot-le (suc n) (inl y) = ord-bot-le n y
ord-bot-le (suc n) (inr _) = ⋆

-- ord-suc preserves the ordering

ord-suc-mono : (n : ℕ) (x y : Ord (suc n))
  → _≤Ord_ {suc n} x y
  → _≤Ord_ {suc (suc n)} (ord-suc n x) (ord-suc n y)
ord-suc-mono zero (inl ⋆) (inl ⋆) _ = ⋆
ord-suc-mono zero (inl ⋆) (inr ⋆) _ = ⋆
ord-suc-mono zero (inr ⋆) (inl ⋆) ()
ord-suc-mono zero (inr ⋆) (inr ⋆) _ = ⋆
ord-suc-mono (suc n) (inl x) (inl y) le = ord-suc-mono n x y le
ord-suc-mono (suc n) (inl _) (inr ⋆) _ = ⋆
ord-suc-mono (suc n) (inr ⋆) (inl _) ()
ord-suc-mono (suc n) (inr ⋆) (inr ⋆) _ = ⋆

-- The bottom ordinal is ≤ any ord-suc value

ord-bot-le-suc : (n : ℕ) (y : Ord (suc n))
  → _≤Ord_ {suc (suc n)} (inl (ord-bot n)) (ord-suc n y)
ord-bot-le-suc zero (inl ⋆) = ⋆
ord-bot-le-suc zero (inr ⋆) = ⋆
ord-bot-le-suc (suc n) (inl y) = ord-bot-le-suc n y
ord-bot-le-suc (suc n) (inr ⋆) = any-≤Ord-top (inl (ord-bot n))

-- monotone-ord-fwd preserves pointwise ordering

monotone-ord-fwd-mono : (n : ℕ) (w₁ w₂ : MonotoneOrd n)
  → ((o : Ord n) → pr₁ w₁ o ≤𝟚 pr₁ w₂ o)
  → _≤Ord_ {suc n} (monotone-ord-fwd n w₁) (monotone-ord-fwd n w₂)

monotone-ord-fwd-mono-suc : (n : ℕ)
  (q₁ q₂ : Ord (suc n) → 𝟚)
  (mono₁ : is-monotone-Ord {suc n} q₁)
  (mono₂ : is-monotone-Ord {suc n} q₂)
  → ((o : Ord (suc n)) → q₁ o ≤𝟚 q₂ o)
  → (b₁ b₂ : 𝟚) → q₁ (inr ⋆) ≡ b₁ → q₂ (inr ⋆) ≡ b₂
  → _≤Ord_ {suc (suc n)}
      (monotone-ord-fwd-suc n b₁
        ((λ x → q₁ (inl x)) , (λ x y le → mono₁ (inl x) (inl y) le)))
      (monotone-ord-fwd-suc n b₂
        ((λ x → q₂ (inl x)) , (λ x y le → mono₂ (inl x) (inl y) le)))

monotone-ord-fwd-mono zero (q₁ , m₁) (q₂ , m₂) pw =
  fwd-mono-0 (q₁ ⋆) (q₂ ⋆) (pw ⋆)
  where
    fwd-mono-0 : (a b : 𝟚) → a ≤𝟚 b → _≤Ord_ {suc zero} a b
    fwd-mono-0 (inl _) (inl _) _ = ⋆
    fwd-mono-0 (inl _) (inr _) _ = ⋆
    fwd-mono-0 (inr _) (inl _) ()
    fwd-mono-0 (inr _) (inr _) _ = ⋆

monotone-ord-fwd-mono (suc n) (q₁ , mono₁) (q₂ , mono₂) pw =
  monotone-ord-fwd-mono-suc n q₁ q₂ mono₁ mono₂ pw
    (q₁ (inr ⋆)) (q₂ (inr ⋆)) (refl _) (refl _)

monotone-ord-fwd-mono-suc n q₁ q₂ mono₁ mono₂ pw (inl ⋆) (inl ⋆) p₁ p₂ =
  monotone-ord-fwd-mono n
    ((λ x → q₁ (inl x)) , (λ x y le → mono₁ (inl x) (inl y) le))
    ((λ x → q₂ (inl x)) , (λ x y le → mono₂ (inl x) (inl y) le))
    (λ o → pw (inl o))

monotone-ord-fwd-mono-suc n q₁ q₂ mono₁ mono₂ pw (inl ⋆) (inr ⋆) p₁ p₂ =
  transport (λ z → _≤Ord_ {suc (suc n)} (inl z) (ord-suc n (monotone-ord-fwd n w₂₀)))
    (fwd-bot ⁻¹) (ord-bot-le-suc n (monotone-ord-fwd n w₂₀))
  where
    w₁₀ = ((λ x → q₁ (inl x)) , (λ x y le → mono₁ (inl x) (inl y) le))
    w₂₀ = ((λ x → q₂ (inl x)) , (λ x y le → mono₂ (inl x) (inl y) le))
    all-zero : (z : Ord (suc n)) → q₁ z ≡ inl ⋆
    all-zero = all-const-from-top q₁ mono₁ p₁
    w₁₀-eq : w₁₀ ≡ ((λ _ → inl ⋆) , (λ _ _ _ → ⋆))
    w₁₀-eq = to-Σ-≡ (funext (λ x → all-zero (inl x)) ,
                       is-monotone-Ord-is-prop (λ _ → inl ⋆) _ _)
    fwd-bot : monotone-ord-fwd n w₁₀ ≡ ord-bot n
    fwd-bot = ap (monotone-ord-fwd n) w₁₀-eq ∙ fwd-all-zeros n

monotone-ord-fwd-mono-suc n q₁ q₂ mono₁ mono₂ pw (inr ⋆) (inl ⋆) p₁ p₂ =
  𝟘-elim (transport (λ b → inr ⋆ ≤𝟚 b) p₂
    (transport (λ a → a ≤𝟚 q₂ (inr ⋆)) p₁ (pw (inr ⋆))))

monotone-ord-fwd-mono-suc n q₁ q₂ mono₁ mono₂ pw (inr ⋆) (inr ⋆) p₁ p₂ =
  ord-suc-mono n
    (monotone-ord-fwd n w₁₀)
    (monotone-ord-fwd n w₂₀)
    (monotone-ord-fwd-mono n w₁₀ w₂₀ (λ o → pw (inl o)))
  where
    w₁₀ = ((λ x → q₁ (inl x)) , (λ x y le → mono₁ (inl x) (inl y) le))
    w₂₀ = ((λ x → q₂ (inl x)) , (λ x y le → mono₂ (inl x) (inl y) le))

------------------------------------------------------------------------
-- Categorical monotonicity is a proposition
------------------------------------------------------------------------

is-monotone-is-prop : {C : Cat} (p : Ob C → 𝟚) → is-prop (is-monotone {C} p)
is-monotone-is-prop p = Π-is-prop (λ m → ≤𝟚-is-prop (p (dom m)) (p (cod m)))

-- Transport ≤𝟚 along paths in both arguments

≤𝟚-transport : {a a' b b' : 𝟚} → a ≡ a' → b ≡ b' → a ≤𝟚 b → a' ≤𝟚 b'
≤𝟚-transport (refl _) (refl _) h = h

-- Transitivity of ≤𝟚

≤𝟚-trans : {a b c : 𝟚} → a ≤𝟚 b → b ≤𝟚 c → a ≤𝟚 c
≤𝟚-trans {inl _} {_}     {_}     _ _ = ⋆
≤𝟚-trans {inr _} {inl _} {_}     () _
≤𝟚-trans {inr _} {inr _} {inl _} _ ()
≤𝟚-trans {inr _} {inr _} {inr _} _ _ = ⋆

------------------------------------------------------------------------
-- Pointwise ordering preservation for monotone-ord-bwd
--
-- monotone-ord-bwd sends ordered ordinals to pointwise-ordered
-- monotone functions.  The proof uses ord-unsuc-mono to show that
-- ord-unsuc preserves order, and bwd-aux-pw for the auxiliary map.
------------------------------------------------------------------------

-- The classification order on 𝟙 + Ord (suc n)

_≤class_ : {n : ℕ} → 𝟙 + Ord (suc n) → 𝟙 + Ord (suc n) → Type 𝓤₀
_≤class_ (inl _) _       = 𝟙
_≤class_ (inr _) (inl _) = 𝟘
_≤class_ {n} (inr x) (inr y) = _≤Ord_ {suc n} x y

-- ord-unsuc-lift preserves the classification order

ord-unsuc-lift-mono : (n : ℕ) (a b : 𝟙 + Ord (suc n))
  → _≤class_ {n} a b → _≤class_ {suc n} (ord-unsuc-lift n a) (ord-unsuc-lift n b)
ord-unsuc-lift-mono n (inl ⋆) _ _ = ⋆
ord-unsuc-lift-mono n (inr _) (inl _) ()
ord-unsuc-lift-mono n (inr _) (inr _) le = le

-- Any lifted value is ≤class the second-to-top classification

ord-unsuc-lift-le-top : (n : ℕ) (r : 𝟙 + Ord (suc n))
  → _≤class_ {suc n} (ord-unsuc-lift n r) (inr (inl (inr ⋆)))
ord-unsuc-lift-le-top n (inl ⋆) = ⋆
ord-unsuc-lift-le-top n (inr c) = any-≤Ord-top c

-- Any lifted value is ≤class the top classification

ord-unsuc-lift-le-rrtop : (n : ℕ) (r : 𝟙 + Ord (suc n))
  → _≤class_ {suc n} (ord-unsuc-lift n r) (inr (inr ⋆))
ord-unsuc-lift-le-rrtop n (inl ⋆) = ⋆
ord-unsuc-lift-le-rrtop n (inr _) = ⋆

-- ord-unsuc preserves order

ord-unsuc-mono : (n : ℕ) (x y : Ord (suc (suc n)))
  → _≤Ord_ {suc (suc n)} x y → _≤class_ {n} (ord-unsuc n x) (ord-unsuc n y)
ord-unsuc-mono zero (inl (inl ⋆)) _ _ = ⋆
ord-unsuc-mono zero (inl (inr ⋆)) (inl (inl ⋆)) ()
ord-unsuc-mono zero (inl (inr ⋆)) (inl (inr ⋆)) _ = ⋆
ord-unsuc-mono zero (inl (inr ⋆)) (inr ⋆) _ = ⋆
ord-unsuc-mono zero (inr ⋆) (inl _) ()
ord-unsuc-mono zero (inr ⋆) (inr ⋆) _ = ⋆
ord-unsuc-mono (suc n) (inl (inl x')) (inl (inl y')) le =
  ord-unsuc-lift-mono n (ord-unsuc n (inl x')) (ord-unsuc n (inl y'))
    (ord-unsuc-mono n (inl x') (inl y') le)
ord-unsuc-mono (suc n) (inl (inl x')) (inl (inr ⋆)) _ =
  ord-unsuc-lift-le-top n (ord-unsuc n (inl x'))
ord-unsuc-mono (suc n) (inl (inl x')) (inr ⋆) _ =
  ord-unsuc-lift-le-rrtop n (ord-unsuc n (inl x'))
ord-unsuc-mono (suc n) (inl (inr ⋆)) (inl (inl _)) ()
ord-unsuc-mono (suc n) (inl (inr ⋆)) (inl (inr ⋆)) _ = ⋆
ord-unsuc-mono (suc n) (inl (inr ⋆)) (inr ⋆) _ = ⋆
ord-unsuc-mono (suc n) (inr ⋆) (inl _) ()
ord-unsuc-mono (suc n) (inr ⋆) (inr ⋆) _ = ⋆

-- bwd-aux preserves pointwise ordering (mutually recursive with below)

bwd-aux-pw : (n : ℕ) (a b : 𝟙 + Ord (suc n)) → _≤class_ {n} a b
  → (o : Ord (suc n))
  → pr₁ (monotone-ord-bwd-aux n a) o ≤𝟚 pr₁ (monotone-ord-bwd-aux n b) o
monotone-ord-bwd-pw : (n : ℕ) (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
  → (o : Ord n) → pr₁ (monotone-ord-bwd n x) o ≤𝟚 pr₁ (monotone-ord-bwd n y) o

bwd-aux-pw n (inl ⋆) _ _ _ = ⋆
bwd-aux-pw n (inr _) (inl _) ()
bwd-aux-pw n (inr _) (inr _) _ (inr ⋆) = ⋆
bwd-aux-pw n (inr cx) (inr cy) le (inl z) =
  monotone-ord-bwd-pw n cx cy le z

monotone-ord-bwd-pw zero (inl ⋆) _ _ ⋆ = ⋆
monotone-ord-bwd-pw zero (inr ⋆) (inl ⋆) ()
monotone-ord-bwd-pw zero (inr ⋆) (inr ⋆) _ ⋆ = ⋆
monotone-ord-bwd-pw (suc k) x y le o =
  bwd-aux-pw k (ord-unsuc k x) (ord-unsuc k y) (ord-unsuc-mono k x y le) o

------------------------------------------------------------------------
-- Transfer: categorical monotonicity ≃ order-theoretic monotonicity
--
-- Base case: For Δ 0 = 𝟏c, both Ob(𝟏c) and 𝟙 have one element, so
-- both monotonicity conditions are trivially satisfied and the
-- equivalence reduces to (Ob 𝟏c → 𝟚) ≃ (𝟙 → 𝟚).
--
-- Step case: Requires relating morphisms in Fun(Δ n, 𝕀) to the
-- order ≤Ord on Ord(suc n). This involves the exponential adjunction
-- and the Segal/Rezk conditions; we postulate it given the IH.
------------------------------------------------------------------------

monotone-transfer-0 : Monotone (Δ zero) ≃ MonotoneOrd zero
monotone-transfer-0 = fwd , invertible-to-equiv fwd (bwd , rinv , linv)
  where
    c₀ : Ob 𝟏c
    c₀ = center (terminal 𝟏c)
    φ : (x : Ob 𝟏c) → c₀ ≡ x
    φ = centrality (terminal 𝟏c)

    fwd : Monotone 𝟏c → MonotoneOrd zero
    fwd (p , _) = (λ _ → p c₀) , (λ _ _ _ → ≤𝟚-refl (p c₀))

    bwd : MonotoneOrd zero → Monotone 𝟏c
    bwd (q , _) = (λ _ → q ⋆) , (λ _ → ≤𝟚-refl (q ⋆))

    rinv : (w : MonotoneOrd zero) → fwd (bwd w) ≡ w
    rinv (q , mono) =
      to-Σ-≡ (funext (𝟙-induction _ (refl (q ⋆))) ,
               is-monotone-Ord-is-prop q _ mono)

    linv : (w : Monotone 𝟏c) → bwd (fwd w) ≡ w
    linv (p , mono) =
      to-Σ-≡ (funext (λ x → ap p (φ x)) ,
               is-monotone-is-prop p _ mono)

------------------------------------------------------------------------
-- Helper for building monotone-transfer at successor levels
--
-- Given the object equivalence e : Ob(Δ(suc n)) ≃ Ord(suc n),
-- together with two propositional facts (preservation and reflection
-- of monotonicity), constructs Monotone(Δ(suc n)) ≃ MonotoneOrd(suc n).
------------------------------------------------------------------------

build-mt-suc : (n : ℕ) (e : Ob (Δ (suc n)) ≃ Ord (suc n))
  → ((p : Ob (Δ (suc n)) → 𝟚) → is-monotone {Δ (suc n)} p
       → is-monotone-Ord {suc n} (λ x → p (equiv-inv e x)))
  → ((p : Ob (Δ (suc n)) → 𝟚) → is-monotone-Ord {suc n} (λ x → p (equiv-inv e x))
       → is-monotone {Δ (suc n)} p)
  → Monotone (Δ (suc n)) ≃ MonotoneOrd (suc n)
build-mt-suc n e pres-pf refl-pf =
  fwd , invertible-to-equiv fwd (bwd , rinv , linv)
  where
    fwd : Monotone (Δ (suc n)) → MonotoneOrd (suc n)
    fwd (p , mono) =
      (λ x → p (equiv-inv e x)) , pres-pf p mono

    bwd : MonotoneOrd (suc n) → Monotone (Δ (suc n))
    bwd (q , mono') =
      (λ x → q (pr₁ e x)) ,
      refl-pf (λ x → q (pr₁ e x))
        (transport (λ r → is-monotone-Ord {suc n} r)
          ((funext (λ x → ap q (equiv-inv-rinv e x))) ⁻¹)
          mono')

    rinv : (w : MonotoneOrd (suc n)) → fwd (bwd w) ≡ w
    rinv (q , mono') =
      to-Σ-≡ (funext (λ x → ap q (equiv-inv-rinv e x)) ,
               is-monotone-Ord-is-prop q _ mono')

    linv : (w : Monotone (Δ (suc n))) → bwd (fwd w) ≡ w
    linv (p , mono) =
      to-Σ-≡ (funext (λ x → ap p (equiv-inv-linv e x)) ,
               is-monotone-is-prop p _ mono)

------------------------------------------------------------------------
-- Interpolation on 𝟚 (helper for pointwise-to-mor)
--
-- interp selects between two values based on a 𝟚 flag:
--   interp 0 a b = a,  interp 1 a b = b.
------------------------------------------------------------------------

interp : 𝟚 → 𝟚 → 𝟚 → 𝟚
interp (inl _) a b = a
interp (inr _) a b = b

interp-mono : (i₁ i₂ a₁ a₂ b₁ b₂ : 𝟚) → i₁ ≤𝟚 i₂
  → a₁ ≤𝟚 a₂ → b₁ ≤𝟚 b₂ → a₂ ≤𝟚 b₂
  → interp i₁ a₁ b₁ ≤𝟚 interp i₂ a₂ b₂
interp-mono (inl _) (inl _) _ _ _ _ _ ha _ _ = ha
interp-mono (inl _) (inr _) _ _ _ _ _ ha _ hab = ≤𝟚-trans ha hab
interp-mono (inr _) (inl _) _ _ _ _ () _ _ _
interp-mono (inr _) (inr _) _ _ _ _ _ _ hb _ = hb

interp-cong : {i₁ i₂ a₁ a₂ b₁ b₂ : 𝟚}
  → i₁ ≡ i₂ → a₁ ≡ a₂ → b₁ ≡ b₂ → interp i₁ a₁ b₁ ≡ interp i₂ a₂ b₂
interp-cong (refl _) (refl _) (refl _) = refl _

------------------------------------------------------------------------
-- equiv-inv distributes over equiv-comp (propositional, not definitional)
--
-- Proof: use the round-trip properties equiv-inv-rinv and equiv-inv-linv
-- to build a path  equiv-inv (comp e₁ e₂) c ≡ equiv-inv e₁ (equiv-inv e₂ c).
------------------------------------------------------------------------

equiv-inv-comp : {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
  (e₁ : A ≃ B) (e₂ : B ≃ C) (c : C)
  → equiv-inv (equiv-comp e₁ e₂) c ≡ equiv-inv e₁ (equiv-inv e₂ c)
equiv-inv-comp e₁ e₂ c =
  ap (equiv-inv (equiv-comp e₁ e₂)) (chain ⁻¹)
  ∙ equiv-inv-linv (equiv-comp e₁ e₂) (equiv-inv e₁ (equiv-inv e₂ c))
  where
    chain : pr₁ (equiv-comp e₁ e₂) (equiv-inv e₁ (equiv-inv e₂ c)) ≡ c
    chain = ap (pr₁ e₂) (equiv-inv-rinv e₁ (equiv-inv e₂ c))
            ∙ equiv-inv-rinv e₂ c

------------------------------------------------------------------------
-- Pointwise extraction from 𝕀-char-rinv
--
-- 𝕀-char-rinv gives a path in Monotone C.  Projecting out the first
-- component and evaluating at z gives a pointwise equation:
-- ob-to-𝟚 (𝕀-char-inverse C w) z ≡ pr₁ w z.
------------------------------------------------------------------------

𝕀-char-ob-to-𝟚 : (C : Cat) (w : Monotone C) (z : Ob C)
  → ob-to-𝟚 (𝕀-char-inverse C w) z ≡ pr₁ w z
𝕀-char-ob-to-𝟚 C w z = ap (λ f → pr₁ f z) (𝕀-char-rinv C w)

------------------------------------------------------------------------
-- Hom coercion along paths
------------------------------------------------------------------------

Hom-coerce : {C : Cat} {a a' b b' : Ob C}
  → a' ≡ a → b' ≡ b → Hom C a' b' → Hom C a b
Hom-coerce pa pb (m , dm , cm) = m , dm ∙ pa , cm ∙ pb

------------------------------------------------------------------------
-- Product cone equality (generalization of cone-eq-𝟏c)
------------------------------------------------------------------------

prod-cone-eq : (A B X : Cat)
  → {h₁ h₂ : Map X A} {k₁ k₂ : Map X B}
  → {p₁ : comp (! A) h₁ ≡ comp (! B) k₁}
  → {p₂ : comp (! A) h₂ ≡ comp (! B) k₂}
  → h₁ ≡ h₂ → k₁ ≡ k₂
  → (h₁ , k₁ , p₁) ≡ (h₂ , k₂ , p₂)
prod-cone-eq A B X (refl _) (refl _) =
  to-Σ-≡ (refl _ , to-Σ-≡ (refl _ ,
    props-are-sets (singletons-are-props (terminal X)) _ _ _ _))

------------------------------------------------------------------------
-- Naturality of pairing and congruence
------------------------------------------------------------------------

pair-nat : {A B X Y : Cat} (g₁ : Map X A) (g₂ : Map X B) (f : Map Y X)
  → comp ⟨ g₁ , g₂ ⟩ f ≡ ⟨ comp g₁ f , comp g₂ f ⟩
pair-nat {A} {B} {X} {Y} g₁ g₂ f = equiv-inj
  (pb-comparison (! A) (! B) Y)
  (pb-is-equiv (! A) (! B) Y)
  (prod-cone-eq A B Y
    (comp-assoc (π₁ A B) ⟨ g₁ , g₂ ⟩ f
     ∙ ap (λ h → comp h f) (pair-β₁ g₁ g₂)
     ∙ (pair-β₁ (comp g₁ f) (comp g₂ f)) ⁻¹)
    (comp-assoc (π₂ A B) ⟨ g₁ , g₂ ⟩ f
     ∙ ap (λ h → comp h f) (pair-β₂ g₁ g₂)
     ∙ (pair-β₂ (comp g₁ f) (comp g₂ f)) ⁻¹))

pair-ap : {A B X : Cat} {h₁ h₂ : Map X A} {k₁ k₂ : Map X B}
  → h₁ ≡ h₂ → k₁ ≡ k₂ → ⟨ h₁ , k₁ ⟩ ≡ ⟨ h₂ , k₂ ⟩
pair-ap (refl _) (refl _) = refl _

------------------------------------------------------------------------
-- pointwise-to-mor: a pointwise ordering of functors into 𝕀
-- yields a morphism in Fun(C, 𝕀).
--
-- Proof: build h : 𝕀 ×c C → 𝕀 interpolating f₁ and f₂ via 𝕀-char,
-- transpose to η : 𝕀 → Fun(C, 𝕀) via exp-equiv, then verify endpoints
-- using 𝕀-char injectivity and ob-map-equiv injectivity.
------------------------------------------------------------------------

pointwise-to-mor : (C : Cat) (f₁ f₂ : Map C 𝕀)
    → ((z : Ob C) → ob-to-𝟚 f₁ z ≤𝟚 ob-to-𝟚 f₂ z)
    → Hom (Fun C 𝕀) (map-to-ob C 𝕀 f₁) (map-to-ob C 𝕀 f₂)
pointwise-to-mor C f₁ f₂ pw = η , dom-pf , cod-pf
  where
    p : Ob (𝕀 ×c C) → 𝟚
    p u = interp (pr₁ 𝕀-ob (comp (π₁ 𝕀 C) u))
                 (ob-to-𝟚 f₁ (comp (π₂ 𝕀 C) u))
                 (ob-to-𝟚 f₂ (comp (π₂ 𝕀 C) u))

    mono : is-monotone {𝕀 ×c C} p
    mono m' = interp-mono
      (pr₁ 𝕀-ob (comp (π₁ 𝕀 C) (dom m')))
      (pr₁ 𝕀-ob (comp (π₁ 𝕀 C) (cod m')))
      (ob-to-𝟚 f₁ (comp (π₂ 𝕀 C) (dom m')))
      (ob-to-𝟚 f₁ (comp (π₂ 𝕀 C) (cod m')))
      (ob-to-𝟚 f₂ (comp (π₂ 𝕀 C) (dom m')))
      (ob-to-𝟚 f₂ (comp (π₂ 𝕀 C) (cod m')))
      (≤𝟚-transport
        (ap (pr₁ 𝕀-ob) (dom-nat (π₁ 𝕀 C) m'))
        (ap (pr₁ 𝕀-ob) (cod-nat (π₁ 𝕀 C) m'))
        (𝕀-mor-order (comp (π₁ 𝕀 C) m')))
      (≤𝟚-transport
        (ap (pr₁ 𝕀-ob) (dom-nat f₁ (comp (π₂ 𝕀 C) m')
          ∙ ap (comp f₁) (dom-nat (π₂ 𝕀 C) m')))
        (ap (pr₁ 𝕀-ob) (cod-nat f₁ (comp (π₂ 𝕀 C) m')
          ∙ ap (comp f₁) (cod-nat (π₂ 𝕀 C) m')))
        (𝕀-mor-order (comp f₁ (comp (π₂ 𝕀 C) m'))))
      (≤𝟚-transport
        (ap (pr₁ 𝕀-ob) (dom-nat f₂ (comp (π₂ 𝕀 C) m')
          ∙ ap (comp f₂) (dom-nat (π₂ 𝕀 C) m')))
        (ap (pr₁ 𝕀-ob) (cod-nat f₂ (comp (π₂ 𝕀 C) m')
          ∙ ap (comp f₂) (cod-nat (π₂ 𝕀 C) m')))
        (𝕀-mor-order (comp f₂ (comp (π₂ 𝕀 C) m'))))
      (pw (comp (π₂ 𝕀 C) (cod m')))

    h : Map (𝕀 ×c C) 𝕀
    h = 𝕀-char-inverse (𝕀 ×c C) (p , mono)

    η : Mor (Fun C 𝕀)
    η = equiv-inv (exp-equiv C 𝕀 𝕀) h

    η-rt : exp-comparison C 𝕀 𝕀 η ≡ h
    η-rt = equiv-inv-rinv (exp-equiv C 𝕀 𝕀) h

    slice : Ob 𝕀 → Map C (𝕀 ×c C)
    slice v = ⟨ comp v (! C) , idMap C ⟩

    lhs-chain : (v : Ob 𝕀)
      → ob-to-map C 𝕀 (comp η v)
        ≡ comp (ev C 𝕀) ⟨ comp η (comp v (! C)) , idMap C ⟩
    lhs-chain v =
      (comp-assoc (ev C 𝕀)
        ⟨ comp (comp η v) (π₁ 𝟏c C) , π₂ 𝟏c C ⟩ (unit-right C)) ⁻¹
      ∙ ap (comp (ev C 𝕀))
          (pair-nat (comp (comp η v) (π₁ 𝟏c C)) (π₂ 𝟏c C) (unit-right C)
           ∙ pair-ap
               ((comp-assoc (comp η v) (π₁ 𝟏c C) (unit-right C)) ⁻¹
                ∙ ap (comp (comp η v)) (pair-β₁ (! C) (idMap C))
                ∙ (comp-assoc η v (! C)) ⁻¹)
               (pair-β₂ (! C) (idMap C)))

    rhs-chain : (v : Ob 𝕀)
      → comp h (slice v)
        ≡ comp (ev C 𝕀) ⟨ comp η (comp v (! C)) , idMap C ⟩
    rhs-chain v =
      ap (λ g → comp g (slice v)) (η-rt ⁻¹)
      ∙ (comp-assoc (ev C 𝕀)
          ⟨ comp η (π₁ 𝕀 C) , π₂ 𝕀 C ⟩ (slice v)) ⁻¹
      ∙ ap (comp (ev C 𝕀))
          (pair-nat (comp η (π₁ 𝕀 C)) (π₂ 𝕀 C) (slice v)
           ∙ pair-ap
               ((comp-assoc η (π₁ 𝕀 C) (slice v)) ⁻¹
                ∙ ap (comp η) (pair-β₁ (comp v (! C)) (idMap C)))
               (pair-β₂ (comp v (! C)) (idMap C)))

    ob-to-map-eq : (v : Ob 𝕀)
      → ob-to-map C 𝕀 (comp η v) ≡ comp h (slice v)
    ob-to-map-eq v = lhs-chain v ∙ (rhs-chain v) ⁻¹

    π₁-slice : (v : Ob 𝕀) (z : Ob C)
      → comp (π₁ 𝕀 C) (comp (slice v) z) ≡ v
    π₁-slice v z =
      comp-assoc (π₁ 𝕀 C) (slice v) z
      ∙ ap (λ g → comp g z) (pair-β₁ (comp v (! C)) (idMap C))
      ∙ (comp-assoc v (! C) z) ⁻¹
      ∙ ap (comp v)
          (singletons-are-props (terminal 𝟏c) (comp (! C) z) (idMap 𝟏c))
      ∙ comp-id-r v

    π₂-slice : (v : Ob 𝕀) (z : Ob C)
      → comp (π₂ 𝕀 C) (comp (slice v) z) ≡ z
    π₂-slice v z =
      comp-assoc (π₂ 𝕀 C) (slice v) z
      ∙ ap (λ g → comp g z) (pair-β₂ (comp v (! C)) (idMap C))
      ∙ comp-id-l z

    h-slice-pw : (v : Ob 𝕀) (z : Ob C)
      → ob-to-𝟚 (comp h (slice v)) z
        ≡ interp (pr₁ 𝕀-ob v) (ob-to-𝟚 f₁ z) (ob-to-𝟚 f₂ z)
    h-slice-pw v z =
      ap (pr₁ 𝕀-ob) ((comp-assoc h (slice v) z) ⁻¹)
      ∙ 𝕀-char-ob-to-𝟚 (𝕀 ×c C) (p , mono) (comp (slice v) z)
      ∙ interp-cong
          (ap (pr₁ 𝕀-ob) (π₁-slice v z))
          (ap (ob-to-𝟚 f₁) (π₂-slice v z))
          (ap (ob-to-𝟚 f₂) (π₂-slice v z))

    h-slice₀-eq : comp h (slice 𝕀₀) ≡ f₁
    h-slice₀-eq = equiv-inj (𝕀-char-comparison C) (pr₂ (𝕀-char C))
      (to-Σ-≡ (funext (λ z →
        h-slice-pw 𝕀₀ z
        ∙ interp-cong (equiv-inv-rinv 𝕀-ob (inl ⋆)) (refl _) (refl _)) ,
       is-monotone-is-prop (ob-to-𝟚 f₁) _ _))

    h-slice₁-eq : comp h (slice 𝕀₁) ≡ f₂
    h-slice₁-eq = equiv-inj (𝕀-char-comparison C) (pr₂ (𝕀-char C))
      (to-Σ-≡ (funext (λ z →
        h-slice-pw 𝕀₁ z
        ∙ interp-cong (equiv-inv-rinv 𝕀-ob (inr ⋆)) (refl _) (refl _)) ,
       is-monotone-is-prop (ob-to-𝟚 f₂) _ _))

    dom-pf : dom η ≡ map-to-ob C 𝕀 f₁
    dom-pf = equiv-inj (ob-to-map C 𝕀) (pr₂ (ob-map-equiv C 𝕀))
      (ob-to-map-eq 𝕀₀ ∙ h-slice₀-eq ∙ (ob-map-roundtrip₁ C 𝕀 f₁) ⁻¹)

    cod-pf : cod η ≡ map-to-ob C 𝕀 f₂
    cod-pf = equiv-inj (ob-to-map C 𝕀) (pr₂ (ob-map-equiv C 𝕀))
      (ob-to-map-eq 𝕀₁ ∙ h-slice₁-eq ∙ (ob-map-roundtrip₁ C 𝕀 f₂) ⁻¹)

------------------------------------------------------------------------
-- A morphism in Fun(C, 𝕀) gives pointwise ≤𝟚 ordering on objects.
--
-- Proof: define the evaluation-at-z functor  ev-z : Fun(C,𝕀) → 𝕀
-- by  ev-z = ev ∘ ⟨ id, const z ⟩.  Then comp ev-z m is a morphism
-- in 𝕀, so 𝕀-mor-order gives the ordering.  The key equation
-- comp ev-z f ≡ comp (ob-to-map f) z  follows because both sides
-- reduce to  ev ⟨ f, z ⟩  after unwinding definitions.
------------------------------------------------------------------------

mor-to-pointwise : (C : Cat) (m : Mor (Fun C 𝕀)) (z : Ob C)
  → ob-to-𝟚 (ob-to-map C 𝕀 (dom m)) z
    ≤𝟚 ob-to-𝟚 (ob-to-map C 𝕀 (cod m)) z
mor-to-pointwise C m z = ≤𝟚-transport p-dom p-cod (𝕀-mor-order (comp ev-z m))
  where
    F = Fun C 𝕀
    ev-z : Map F 𝕀
    ev-z = comp (ev C 𝕀) ⟨ idMap F , comp z (! F) ⟩
    bang-cancel : (f : Ob F) → comp (comp z (! F)) f ≡ z
    bang-cancel f =
      (comp-assoc z (! F) f) ⁻¹
      ∙ ap (comp z) (singletons-are-props (terminal 𝟏c) (comp (! F) f) (idMap 𝟏c))
      ∙ comp-id-r z
    ev-z-lhs : (f : Ob F) → comp ev-z f ≡ comp (ev C 𝕀) ⟨ f , z ⟩
    ev-z-lhs f =
      (comp-assoc (ev C 𝕀) ⟨ idMap F , comp z (! F) ⟩ f) ⁻¹
      ∙ ap (comp (ev C 𝕀))
          (pair-nat (idMap F) (comp z (! F)) f
           ∙ pair-ap (comp-id-l f) (bang-cancel f))
    rhs-first : (f : Ob F)
      → comp (comp f (π₁ 𝟏c C)) (comp (unit-right C) z) ≡ f
    rhs-first f =
      (comp-assoc f (π₁ 𝟏c C) (comp (unit-right C) z)) ⁻¹
      ∙ ap (comp f)
          (comp-assoc (π₁ 𝟏c C) (unit-right C) z
           ∙ ap (λ h → comp h z) (pair-β₁ (! C) (idMap C))
           ∙ singletons-are-props (terminal 𝟏c) (comp (! C) z) (idMap 𝟏c))
      ∙ comp-id-r f
    rhs-second : comp (π₂ 𝟏c C) (comp (unit-right C) z) ≡ z
    rhs-second =
      comp-assoc (π₂ 𝟏c C) (unit-right C) z
      ∙ ap (λ h → comp h z) (pair-β₂ (! C) (idMap C))
      ∙ comp-id-l z
    ev-z-rhs : (f : Ob F)
      → comp (ob-to-map C 𝕀 f) z ≡ comp (ev C 𝕀) ⟨ f , z ⟩
    ev-z-rhs f =
      (comp-assoc (exp-comparison C 𝕀 𝟏c f) (unit-right C) z) ⁻¹
      ∙ (comp-assoc (ev C 𝕀) ⟨ comp f (π₁ 𝟏c C) , π₂ 𝟏c C ⟩
          (comp (unit-right C) z)) ⁻¹
      ∙ ap (comp (ev C 𝕀))
          (pair-nat (comp f (π₁ 𝟏c C)) (π₂ 𝟏c C) (comp (unit-right C) z)
           ∙ pair-ap (rhs-first f) rhs-second)
    ev-z-eq : (f : Ob F) → comp ev-z f ≡ comp (ob-to-map C 𝕀 f) z
    ev-z-eq f = ev-z-lhs f ∙ (ev-z-rhs f) ⁻¹
    p-dom : pr₁ 𝕀-ob (dom (comp ev-z m))
      ≡ ob-to-𝟚 (ob-to-map C 𝕀 (dom m)) z
    p-dom = ap (pr₁ 𝕀-ob) (dom-nat ev-z m ∙ ev-z-eq (dom m))
    p-cod : pr₁ 𝕀-ob (cod (comp ev-z m))
      ≡ ob-to-𝟚 (ob-to-map C 𝕀 (cod m)) z
    p-cod = ap (pr₁ 𝕀-ob) (cod-nat ev-z m ∙ ev-z-eq (cod m))

------------------------------------------------------------------------
-- Construction 20, monotone-step, and monotone-transfer
-- (mutually recursive, with propositional postulates)
--
-- construction-20 (suc n) uses monotone-step n
-- monotone-step n uses monotone-transfer n
-- monotone-transfer (suc n) uses construction-20 (suc n)
--
-- The postulates transfer-pres and transfer-refl are propositions
-- stating that construction-20 preserves and reflects monotonicity.
------------------------------------------------------------------------

construction-20 : (n : ℕ) → Ob (Δ n) ≃ Ord n
monotone-step : (n : ℕ) → Monotone (Δ n) ≃ Ord (suc n)
monotone-transfer : (n : ℕ) → Monotone (Δ n) ≃ MonotoneOrd n
transfer-pres : (n : ℕ) (e : Ob (Δ n) ≃ Ord n)
  → ((x y : Ord n) → _≤Ord_ {n} x y
       → Hom (Δ n) (equiv-inv e x) (equiv-inv e y))
  → (p : Ob (Δ n) → 𝟚)
  → is-monotone {Δ n} p
  → is-monotone-Ord {n} (λ x → p (equiv-inv e x))
transfer-refl : (n : ℕ) (p : Ob (Δ n) → 𝟚)
  → is-monotone-Ord {n} (λ x → p (equiv-inv (construction-20 n) x))
  → is-monotone {Δ n} p
ord-to-mor-fn : (n : ℕ) (x y : Ord n) → _≤Ord_ {n} x y
  → Hom (Δ n) (equiv-inv (construction-20 n) x)
               (equiv-inv (construction-20 n) y)

transfer-pointwise : (n : ℕ) (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
  → (z : Ob (Δ n))
  → pr₁ (equiv-inv (monotone-transfer n) (monotone-ord-bwd n x)) z
    ≤𝟚 pr₁ (equiv-inv (monotone-transfer n) (monotone-ord-bwd n y)) z

-- mt-fwd-eq: the forward map of monotone-transfer n at ordinal o
-- equals the underlying function at equiv-inv (construction-20 n) o.
-- Both cases reduce to refl after case-splitting on n.
mt-fwd-eq : (n : ℕ) (w : Monotone (Δ n)) (o : Ord n)
  → pr₁ (pr₁ (monotone-transfer n) w) o ≡ pr₁ w (equiv-inv (construction-20 n) o)

-- mor-reflects-ord: a morphism in Δ(suc n) determines ordinals x ≤ y
-- whose images under equiv-inv are dom and cod.
-- The ordering uses mor-to-pointwise, mt-fwd-eq, and monotone-ord-fwd-mono.
-- The body only references mutual functions at level n (not suc n),
-- so the termination checker sees a strict decrease from transfer-refl.
mor-reflects-ord : (n : ℕ) (m : Mor (Δ (suc n)))
  → Σ x ꞉ Ord (suc n) , Σ y ꞉ Ord (suc n) ,
      (equiv-inv (construction-20 (suc n)) x ≡ dom m) ×
      (equiv-inv (construction-20 (suc n)) y ≡ cod m) ×
      (_≤Ord_ {suc n} x y)

construction-20 zero = contr-equiv-𝟙 (terminal 𝟏c)
construction-20 (suc n) =
  equiv-comp (ob-map-equiv (Δ n) 𝕀)
    (equiv-comp (𝕀-char (Δ n)) (monotone-step n))

monotone-step n = equiv-comp (monotone-transfer n) (monotone-ord n)

monotone-transfer zero = monotone-transfer-0
monotone-transfer (suc n) =
  build-mt-suc n (construction-20 (suc n))
    (transfer-pres (suc n) (construction-20 (suc n)) (ord-to-mor-fn (suc n)))
    (transfer-refl (suc n))

-- Base case: Ord 0 = 𝟙 has one element, so order-monotonicity is trivial.

transfer-pres zero e _ p _ ⋆ ⋆ _ = ≤𝟚-refl (p (equiv-inv e ⋆))

-- Successor case: the morphism builder otm gives a morphism m with
-- dom m ≡ equiv-inv e x and cod m ≡ equiv-inv e y.  Transport the
-- categorical monotonicity mono(m) along these paths.

transfer-pres (suc n) e otm p mono x y le =
  ≤𝟚-transport (ap p dm) (ap p cm) (mono m)
  where
    h  = otm x y le
    m  = pr₁ h
    dm = pr₁ (pr₂ h)
    cm = pr₂ (pr₂ h)

-- Base case: Ob(𝟏c) is contractible, so dom m ≡ cod m for any m.

transfer-refl zero p _ m =
  transport (λ b → p (dom m) ≤𝟚 b)
    (ap p (singletons-are-props (terminal 𝟏c) (dom m) (cod m)))
    (≤𝟚-refl (p (dom m)))

-- Successor case: use mor-reflects-ord to extract ordinals x ≤ y
-- with c20⁻¹(x) ≡ dom m and c20⁻¹(y) ≡ cod m, apply monoOrd,
-- then transport along the paths.

transfer-refl (suc n) p monoOrd m =
  ≤𝟚-transport (ap p dx) (ap p dy) (monoOrd x y le)
  where
    d  = mor-reflects-ord n m
    x  = pr₁ d
    y  = pr₁ (pr₂ d)
    dx = pr₁ (pr₂ (pr₂ d))
    dy = pr₁ (pr₂ (pr₂ (pr₂ d)))
    le = pr₂ (pr₂ (pr₂ (pr₂ d)))

-- Base case: Δ 0 = 𝟏c, Ord 0 = 𝟙, both endpoints are the unique
-- object of 𝟏c.

ord-to-mor-fn zero ⋆ ⋆ _ =
  id-mor (equiv-inv (construction-20 zero) ⋆) ,
  dom-id (equiv-inv (construction-20 zero) ⋆) ,
  cod-id (equiv-inv (construction-20 zero) ⋆)

-- Successor case: unwind equiv-inv (construction-20 (suc n)) through
-- the equivalence chain.  Since equiv-inv distributes over equiv-comp
-- DEFINITIONALLY (invertible-to-equiv), the chain
--   monotone-ord-bwd → equiv-inv monotone-transfer → 𝕀-char-inverse → map-to-ob
-- produces maps fx, fy whose map-to-ob values are definitionally
-- equiv-inv (construction-20 (suc n)) x and y.  The pointwise ordering
-- follows from transfer-pointwise and 𝕀-char-ob-to-𝟚.

ord-to-mor-fn (suc n) x y le = pointwise-to-mor (Δ n) fx fy pw
  where
    mx = equiv-inv (monotone-transfer n) (monotone-ord-bwd n x)
    my = equiv-inv (monotone-transfer n) (monotone-ord-bwd n y)
    fx = 𝕀-char-inverse (Δ n) mx
    fy = 𝕀-char-inverse (Δ n) my
    pw : (z : Ob (Δ n)) → ob-to-𝟚 fx z ≤𝟚 ob-to-𝟚 fy z
    pw z = ≤𝟚-transport
      (𝕀-char-ob-to-𝟚 (Δ n) mx z ⁻¹) (𝕀-char-ob-to-𝟚 (Δ n) my z ⁻¹)
      (transfer-pointwise n x y le z)

-- Base case: equiv-inv (monotone-transfer 0) reduces via bwd of
-- monotone-transfer-0, and monotone-ord-bwd 0 x gives constant x.
-- So the goal is x ≤𝟚 y, which follows from ≤Ord at level 1.

transfer-pointwise zero (inl ⋆) _ _ _ = ⋆
transfer-pointwise zero (inr ⋆) (inl ⋆) ()
transfer-pointwise zero (inr ⋆) (inr ⋆) _ _ = ⋆

-- Successor case: equiv-inv (monotone-transfer (suc k)) w reduces to
-- (λ z → pr₁ w (pr₁ (construction-20 (suc k)) z)).  So the goal
-- becomes pointwise ordering of monotone-ord-bwd at the ordinal
-- pr₁ (construction-20 (suc k)) z, handled by monotone-ord-bwd-pw.

transfer-pointwise (suc k) x y le z =
  monotone-ord-bwd-pw (suc k) x y le (pr₁ (construction-20 (suc k)) z)

mt-fwd-eq zero w ⋆ = refl _
mt-fwd-eq (suc k) w o = refl _

-- Proof of mor-reflects-ord: compute the ordinals x, y from dom m
-- and cod m by applying the forward maps of the equivalence chain
-- (ob-to-map, 𝕀-char-comparison, monotone-transfer n, monotone-ord-fwd).
-- The equiv-inv paths use the round-trips of each component at level n.
-- The ordering follows from mor-to-pointwise and monotone-ord-fwd-mono.

mor-reflects-ord n m = x , y , dx , dy , le
  where
    w-dom : Monotone (Δ n)
    w-dom = 𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 (dom m))
    w-cod : Monotone (Δ n)
    w-cod = 𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 (cod m))
    mo-dom : MonotoneOrd n
    mo-dom = pr₁ (monotone-transfer n) w-dom
    mo-cod : MonotoneOrd n
    mo-cod = pr₁ (monotone-transfer n) w-cod
    x = monotone-ord-fwd n mo-dom
    y = monotone-ord-fwd n mo-cod
    -- Pointwise ordering: mt-fwd-eq bridges MonotoneOrd to ob-to-𝟚,
    -- then mor-to-pointwise gives the ≤𝟚 ordering.
    pw : (o : Ord n) → pr₁ mo-dom o ≤𝟚 pr₁ mo-cod o
    pw o = ≤𝟚-transport
      ((mt-fwd-eq n w-dom o) ⁻¹)
      ((mt-fwd-eq n w-cod o) ⁻¹)
      (mor-to-pointwise (Δ n) m (equiv-inv (construction-20 n) o))
    le : _≤Ord_ {suc n} x y
    le = monotone-ord-fwd-mono n mo-dom mo-cod pw
    -- Path: the backward map (map-to-ob ∘ 𝕀-char-inverse ∘ equiv-inv(mt) ∘ bwd)
    -- applied to x (resp. y) equals dom m (resp. cod m), by round-trips.
    -- Type written in expanded form to avoid mentioning construction-20 (suc n).
    inv-path : (f : Ob (Δ (suc n)))
      → map-to-ob (Δ n) 𝕀
          (𝕀-char-inverse (Δ n)
            (equiv-inv (monotone-transfer n)
              (monotone-ord-bwd n
                (monotone-ord-fwd n
                  (pr₁ (monotone-transfer n)
                    (𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 f)))))))
        ≡ f
    inv-path f =
      ap (λ w → map-to-ob (Δ n) 𝕀
            (𝕀-char-inverse (Δ n)
              (equiv-inv (monotone-transfer n) w)))
        (monotone-ord-linv n
          (pr₁ (monotone-transfer n)
            (𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 f))))
      ∙ ap (λ w → map-to-ob (Δ n) 𝕀 (𝕀-char-inverse (Δ n) w))
          (equiv-inv-linv (monotone-transfer n)
            (𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 f)))
      ∙ ap (map-to-ob (Δ n) 𝕀)
          (𝕀-char-linv (Δ n) (ob-to-map (Δ n) 𝕀 f))
      ∙ ob-map-roundtrip₂ (Δ n) 𝕀 f
    dx = inv-path (dom m)
    dy = inv-path (cod m)
