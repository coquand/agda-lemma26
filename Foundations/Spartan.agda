{-# OPTIONS --without-K --exact-split #-}

module Foundations.Spartan where

open import Agda.Primitive public
  renaming (
    Set to Type ;
    lzero to 𝓤₀ ;
    lsuc to _⁺ ;
    _⊔_ to _⊔_
  )

variable
  𝓤 𝓥 𝓦 : Level

-- Identity function and composition

id : {A : Type 𝓤} → A → A
id x = x

_∘_ : {A : Type 𝓤} {B : Type 𝓥} {C : B → Type 𝓦}
    → ((b : B) → C b) → (f : A → B) → (a : A) → C (f a)
(g ∘ f) x = g (f x)

infixr 9 _∘_

-- The unit type

data 𝟙 : Type 𝓤₀ where
  ⋆ : 𝟙

𝟙-induction : (P : 𝟙 → Type 𝓤) → P ⋆ → (x : 𝟙) → P x
𝟙-induction P p ⋆ = p

-- The empty type

data 𝟘 : Type 𝓤₀ where

𝟘-induction : (P : 𝟘 → Type 𝓤) → (x : 𝟘) → P x
𝟘-induction P ()

𝟘-elim : {A : Type 𝓤} → 𝟘 → A
𝟘-elim = 𝟘-induction (λ _ → _)

¬_ : Type 𝓤 → Type 𝓤
¬ A = A → 𝟘

-- Natural numbers

data ℕ : Type 𝓤₀ where
  zero : ℕ
  suc  : ℕ → ℕ

ℕ-induction : (P : ℕ → Type 𝓤)
            → P zero
            → ((n : ℕ) → P n → P (suc n))
            → (n : ℕ) → P n
ℕ-induction P p₀ pₛ zero    = p₀
ℕ-induction P p₀ pₛ (suc n) = pₛ n (ℕ-induction P p₀ pₛ n)

ℕ-recursion : (A : Type 𝓤) → A → (ℕ → A → A) → ℕ → A
ℕ-recursion A = ℕ-induction (λ _ → A)

-- Binary sum (coproduct)

data _+_ (A : Type 𝓤) (B : Type 𝓥) : Type (𝓤 ⊔ 𝓥) where
  inl : A → A + B
  inr : B → A + B

+-induction : {A : Type 𝓤} {B : Type 𝓥}
            → (P : A + B → Type 𝓦)
            → ((a : A) → P (inl a))
            → ((b : B) → P (inr b))
            → (x : A + B) → P x
+-induction P f g (inl a) = f a
+-induction P f g (inr b) = g b

-- Σ-types

record Σ {A : Type 𝓤} (B : A → Type 𝓥) : Type (𝓤 ⊔ 𝓥) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public

infixr 1 _,_

Sigma : (A : Type 𝓤) (B : A → Type 𝓥) → Type (𝓤 ⊔ 𝓥)
Sigma A B = Σ B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infixr -1 Sigma

-- Binary product as special case of Σ

_×_ : Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
A × B = Σ {A = A} (λ _ → B)

infixr 2 _×_

-- Identity types

data _≡_ {A : Type 𝓤} : A → A → Type 𝓤 where
  refl : (x : A) → x ≡ x

infix 0 _≡_

𝕁 : {A : Type 𝓤}
  → (P : (x y : A) → x ≡ y → Type 𝓥)
  → ((x : A) → P x x (refl x))
  → (x y : A) (p : x ≡ y) → P x y p
𝕁 P f x x (refl x) = f x

-- Transport

transport : {A : Type 𝓤} (P : A → Type 𝓥)
          → {x y : A} → x ≡ y → P x → P y
transport P (refl x) = λ px → px

-- ap (action on paths)

ap : {A : Type 𝓤} {B : Type 𝓥} (f : A → B)
   → {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

-- Symmetry and transitivity

_⁻¹ : {A : Type 𝓤} {x y : A} → x ≡ y → y ≡ x
(refl x) ⁻¹ = refl x

_∙_ : {A : Type 𝓤} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl x ∙ q = q

infixl 7 _⁻¹
infixl 5 _∙_

-- Path algebra

left-inv : {A : Type 𝓤} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl y
left-inv (refl x) = refl (refl x)

right-inv : {A : Type 𝓤} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl x
right-inv (refl _) = refl _

right-unit : {A : Type 𝓤} {x y : A} (p : x ≡ y) → p ∙ refl y ≡ p
right-unit (refl _) = refl _

∙-assoc : {A : Type 𝓤} {x y z w : A}
         (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc (refl _) q r = refl _

ap-comp : {A : Type 𝓤} {B : Type 𝓥} {C : Type 𝓦}
         (g : B → C) (f : A → B)
         {x y : A} (p : x ≡ y)
       → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp g f (refl _) = refl _

-- Equational reasoning combinators

infix  1 begin_
infixr 2 _≡⟨_⟩_
infix  3 _∎

begin_ : {A : Type 𝓤} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡⟨_⟩_ : {A : Type 𝓤} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {A : Type 𝓤} (x : A) → x ≡ x
x ∎ = refl x

-- Homotopies

_∼_ : {A : Type 𝓤} {B : A → Type 𝓥} → ((x : A) → B x) → ((x : A) → B x) → Type (𝓤 ⊔ 𝓥)
f ∼ g = ∀ x → f x ≡ g x

-- Function extensionality (postulated)

postulate
  funext : {A : Type 𝓤} {B : A → Type 𝓥} {f g : (x : A) → B x}
         → f ∼ g → f ≡ g

-- Propositions, sets, and contractible types

is-prop : Type 𝓤 → Type 𝓤
is-prop X = (x y : X) → x ≡ y

is-set : Type 𝓤 → Type 𝓤
is-set X = (x y : X) → is-prop (x ≡ y)

is-contr : Type 𝓤 → Type 𝓤
is-contr X = Σ c ꞉ X , ((x : X) → c ≡ x)

center : {X : Type 𝓤} → is-contr X → X
center (c , _) = c

centrality : {X : Type 𝓤} (i : is-contr X) (x : X) → center i ≡ x
centrality (_ , φ) = φ

-- Fiber and Voevodsky equivalence (all fibers contractible)

fiber : {A : Type 𝓤} {B : Type 𝓥} → (A → B) → B → Type (𝓤 ⊔ 𝓥)
fiber f y = Σ x ꞉ _ , f x ≡ y

is-equiv : {A : Type 𝓤} {B : Type 𝓥} → (A → B) → Type (𝓤 ⊔ 𝓥)
is-equiv f = (y : _) → is-contr (fiber f y)

_≃_ : Type 𝓤 → Type 𝓥 → Type (𝓤 ⊔ 𝓥)
A ≃ B = Σ f ꞉ (A → B) , is-equiv f

-- Quasi-inverse (invertible maps)

invertible : {A : Type 𝓤} {B : Type 𝓥} → (A → B) → Type (𝓤 ⊔ 𝓥)
invertible f = Σ g ꞉ _ , ((f ∘ g) ∼ id) × ((g ∘ f) ∼ id)

-- Contractible types are propositions

singletons-are-props : {X : Type 𝓤} → is-contr X → is-prop X
singletons-are-props (c , φ) x y = (φ x) ⁻¹ ∙ φ y

-- Propositions are sets

props-are-sets : {X : Type 𝓤} → is-prop X → is-set X
props-are-sets h x _ p q = claim _ p ∙ (claim _ q) ⁻¹
  where
    g : ∀ y → x ≡ y
    g = h x
    claim : ∀ y → (r : x ≡ y) → r ≡ (g x) ⁻¹ ∙ g y
    claim _ (refl _) = (left-inv (g _)) ⁻¹

-- Π-types preserve propositions (uses funext)

Π-is-prop : {A : Type 𝓤} {B : A → Type 𝓥}
           → ((x : A) → is-prop (B x))
           → is-prop ((x : A) → B x)
Π-is-prop h f g = funext (λ x → h x (f x) (g x))

-- Characterization of paths in Σ-types

to-Σ-≡ : {A : Type 𝓤} {B : A → Type 𝓥}
        → {x y : A} {b : B x} {b' : B y}
        → (Σ p ꞉ (x ≡ y) , transport B p b ≡ b')
        → (x , b) ≡ (y , b')
to-Σ-≡ (refl _ , refl _) = refl _

-- Being contractible is a proposition

being-contr-is-prop : {X : Type 𝓤} → is-prop (is-contr X)
being-contr-is-prop {𝓤} {X} (c , φ) (c' , φ') =
  to-Σ-≡ (φ c' , Π-is-prop (props-are-sets isp c') _ φ')
  where
    isp : is-prop X
    isp = singletons-are-props (c , φ)

-- Being an equivalence is a proposition

being-equiv-is-prop : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) → is-prop (is-equiv f)
being-equiv-is-prop f = Π-is-prop (λ y → being-contr-is-prop)

-- Identity function is an equivalence

id-is-equiv : (A : Type 𝓤) → is-equiv (id {𝓤} {A})
id-is-equiv A y = (y , refl y) , h
  where
    h : (σ : fiber id y) → (y , refl y) ≡ σ
    h (_ , refl _) = refl _

-- Identity gives equivalence

id-to-equiv : (A B : Type 𝓤) → A ≡ B → A ≃ B
id-to-equiv A A (refl A) = id , id-is-equiv A

-- Univalence axiom

postulate
  univalence : {A B : Type 𝓤} → is-equiv (id-to-equiv A B)
