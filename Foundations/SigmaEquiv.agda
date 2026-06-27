{-# OPTIONS --without-K --exact-split #-}

module Foundations.SigmaEquiv where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval

------------------------------------------------------------------------
-- Path algebra
------------------------------------------------------------------------

double-inv : {A : Type 𝓤} {x y : A} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
double-inv (refl _) = refl _

------------------------------------------------------------------------
-- Transport lemmas
------------------------------------------------------------------------

Σ-path-transport : {A : Type 𝓤} {B : A → Type 𝓥} {w w' : Σ B}
  (c : w ≡ w') → transport B (ap pr₁ c) (pr₂ w) ≡ pr₂ w'
Σ-path-transport (refl _) = refl _

transport-path-l : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {b : B}
  {x y : A} (p : x ≡ y) (r : f x ≡ b)
  → transport (λ a → f a ≡ b) p r ≡ (ap f p) ⁻¹ ∙ r
transport-path-l f (refl _) r = refl r

transport-inv-cancel : {A : Type 𝓤} {P : A → Type 𝓥} {x y : A}
  (p : x ≡ y) (q : P y)
  → transport P p (transport P (p ⁻¹) q) ≡ q
transport-inv-cancel (refl _) q = refl q

transport-comp-family : {A : Type 𝓤} {B : Type 𝓥}
  (f : A → B) {P : B → Type 𝓦} {x y : A}
  (p : x ≡ y) (a : P (f x))
  → transport (P ∘ f) p a ≡ transport P (ap f p) a
transport-comp-family f (refl _) a = refl a

transport-trans : {A : Type 𝓤} {P : A → Type 𝓥} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (a : P x)
  → transport P q (transport P p a) ≡ transport P (p ∙ q) a
transport-trans (refl _) q a = refl _

------------------------------------------------------------------------
-- Half-adjoint coherence for Voevodsky equivalences
--
-- For a Voevodsky equivalence e = (f, ef), the two canonical paths
-- f(f⁻¹(f a)) → f a  coincide:  ap f (linv a) ≡ rinv (f a).
--
-- Proof:  From the centrality path in the fiber of f at f a, extract
-- a transport equation, convert it via transport-path-l, and cancel.
------------------------------------------------------------------------

cancel-left-inv : {A : Type 𝓤} {x y : A} (u : x ≡ y) {p : x ≡ y}
  → u ⁻¹ ∙ p ≡ refl y → p ≡ u
cancel-left-inv (refl _) q = q

equiv-coherence : {A : Type 𝓤} {B : Type 𝓥} (e : A ≃ B) (a : A)
  → ap (pr₁ e) (equiv-inv-linv e a) ≡ equiv-inv-rinv e (pr₁ e a)
equiv-coherence (f , ef) a = (cancel-left-inv u step) ⁻¹
  where
    c = centrality (ef (f a)) (a , refl (f a))
    u = ap f (ap pr₁ c)
    p₀ = pr₂ (center (ef (f a)))
    step : u ⁻¹ ∙ p₀ ≡ refl (f a)
    step = (transport-path-l f (ap pr₁ c) p₀) ⁻¹ ∙ Σ-path-transport c

------------------------------------------------------------------------
-- Σ-change-of-base: base change along an equivalence
--
-- Given e : A ≃ B and P : B → Type, the map
--   (a, p) ↦ (f a, p)  :  Σ(a:A). P(f a) → Σ(b:B). P b
-- is an equivalence.
------------------------------------------------------------------------

Σ-change-of-base : {A : Type 𝓤} {B : Type 𝓥} {P : B → Type 𝓦}
  (e : A ≃ B) → (Σ a ꞉ A , P (pr₁ e a)) ≃ (Σ b ꞉ B , P b)
Σ-change-of-base {P = P} e =
  fwd , invertible-to-equiv fwd (bwd , fwd-bwd , bwd-fwd)
  where
    f = pr₁ e
    fwd : Σ (P ∘ f) → Σ P
    fwd (a , p) = f a , p
    bwd : Σ P → Σ (P ∘ f)
    bwd (b , q) = equiv-inv e b , transport P (equiv-inv-rinv e b ⁻¹) q
    fwd-bwd : (w : Σ P) → fwd (bwd w) ≡ w
    fwd-bwd (b , q) =
      to-Σ-≡ (equiv-inv-rinv e b , transport-inv-cancel (equiv-inv-rinv e b) q)
    bwd-fwd : (w : Σ (P ∘ f)) → bwd (fwd w) ≡ w
    bwd-fwd (a , p) = to-Σ-≡ (equiv-inv-linv e a , fiber-proof)
      where
        fiber-proof : transport (P ∘ f) (equiv-inv-linv e a)
                        (transport P (equiv-inv-rinv e (f a) ⁻¹) p) ≡ p
        fiber-proof =
          transport-comp-family f (equiv-inv-linv e a)
            (transport P (equiv-inv-rinv e (f a) ⁻¹) p)
          ∙ transport-trans (equiv-inv-rinv e (f a) ⁻¹)
              (ap f (equiv-inv-linv e a)) p
          ∙ ap (λ q → transport P q p)
              (ap (λ r → equiv-inv-rinv e (f a) ⁻¹ ∙ r) (equiv-coherence e a)
               ∙ left-inv (equiv-inv-rinv e (f a)))

------------------------------------------------------------------------
-- Σ-fiberwise-equiv: fiberwise equivalences give total equivalences
------------------------------------------------------------------------

Σ-fiberwise-equiv : {A : Type 𝓤} {P Q : A → Type 𝓥}
  → ((a : A) → P a ≃ Q a)
  → Sigma A P ≃ Sigma A Q
Σ-fiberwise-equiv {P = P} {Q = Q} e =
  fwd , invertible-to-equiv fwd (bwd , fwd-bwd , bwd-fwd)
  where
    fwd : Sigma _ P → Sigma _ Q
    fwd (a , p) = a , pr₁ (e a) p
    bwd : Sigma _ Q → Sigma _ P
    bwd (a , q) = a , equiv-inv (e a) q
    fwd-bwd : (w : _) → fwd (bwd w) ≡ w
    fwd-bwd (a , q) = to-Σ-≡ (refl a , equiv-inv-rinv (e a) q)
    bwd-fwd : (w : _) → bwd (fwd w) ≡ w
    bwd-fwd (a , p) = to-Σ-≡ (refl a , equiv-inv-linv (e a) p)

------------------------------------------------------------------------
-- Path equivalences
------------------------------------------------------------------------

path-inv-equiv : {A : Type 𝓤} {x y : A} → (x ≡ y) ≃ (y ≡ x)
path-inv-equiv = _⁻¹ , invertible-to-equiv _⁻¹ (_⁻¹ , double-inv , double-inv)

post-comp-path-equiv : {A : Type 𝓤} {x y z : A}
  → y ≡ z → (x ≡ y) ≃ (x ≡ z)
post-comp-path-equiv (refl _) = id , id-is-equiv _

pre-comp-path-equiv : {A : Type 𝓤} {x y z : A}
  → x ≡ y → (y ≡ z) ≃ (x ≡ z)
pre-comp-path-equiv (refl _) = id , id-is-equiv _
