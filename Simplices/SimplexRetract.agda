{-# OPTIONS --without-K --exact-split #-}

module Simplices.SimplexRetract where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Interval.OrdCompare
open import Simplices.LastEdge
open import Interval.FaceOrd
open import Simplices.FaceMap
open import Simplices.FaceTop
open import Category.ExpEval
open import Simplices.FaceTopProof
open import Interval.FaceOrdCompat
-- pre-comp and pre-face-n inlined from PushoutFun to avoid that dependency
pre-comp : {A A' : Cat} → Map A A' → (B : Cat) → Map (Fun A' B) (Fun A B)
pre-comp {A} {A'} f B =
  equiv-inv (exp-equiv A B (Fun A' B))
    (comp (ev A' B) ⟨ π₁ (Fun A' B) A , comp f (π₂ (Fun A' B) A) ⟩)

pre-face-n : (n : ℕ) → Map (Δ (suc (suc n))) (Δ (suc n))
pre-face-n n = pre-comp (face n) 𝕀

exp-comp-nat : {A B X Y : Cat} (u : Map X (Fun A B)) (v : Map Y X)
  → exp-comparison A B Y (comp u v)
    ≡ comp (exp-comparison A B X u) ⟨ comp v (π₁ Y A) , π₂ Y A ⟩
exp-comp-nat {A} {B} {X} {Y} u v =
  ap (comp (ev A B))
    ((pair-nat (comp u (π₁ X A)) (π₂ X A) ⟨ comp v (π₁ Y A) , π₂ Y A ⟩
      ∙ pair-ap
          ((comp-assoc u (π₁ X A) ⟨ comp v (π₁ Y A) , π₂ Y A ⟩) ⁻¹
           ∙ ap (comp u) (pair-β₁ (comp v (π₁ Y A)) (π₂ Y A))
           ∙ comp-assoc u v (π₁ Y A))
          (pair-β₂ (comp v (π₁ Y A)) (π₂ Y A))) ⁻¹)
  ∙ comp-assoc (ev A B) ⟨ comp u (π₁ X A) , π₂ X A ⟩ ⟨ comp v (π₁ Y A) , π₂ Y A ⟩

------------------------------------------------------------------------
-- Section: Δ(suc(suc n)) → Δ(suc n) ×c 𝕀
--
-- The section s = ⟨pre-face-n n, eval-at-top n⟩ embeds Δ(n+2) into
-- the product Δ(n+1) × 𝕀 by:
--   - first component: restrict φ : Δ(n+1) → 𝕀 along face(n)
--   - second component: evaluate φ at top(n+1)
------------------------------------------------------------------------

eval-at-top : (n : ℕ) → Map (Δ (suc (suc n))) 𝕀
eval-at-top n = comp (ev (Δ (suc n)) 𝕀)
  ⟨ idMap (Δ (suc (suc n))) ,
    comp (top (suc n)) (! (Δ (suc (suc n)))) ⟩

sect : (n : ℕ) → Map (Δ (suc (suc n))) (Δ (suc n) ×c 𝕀)
sect n = ⟨ pre-face-n n , eval-at-top n ⟩

------------------------------------------------------------------------
-- Retraction: Δ(suc n) ×c 𝕀 → Δ(suc(suc n))
--
-- The retraction r sends (σ, t) to the functor
--   y ↦ interp(t, face-ord(suc n, c20(σ), c20(y)), 1)
-- which computes max(face-ord(σ,y), t).
--
-- Construction: define a monotone predicate on
--   (Δ(suc n) ×c 𝕀) ×c Δ(suc n)
-- then use 𝕀-char-inverse and exp-equiv to curry.
------------------------------------------------------------------------

private
  D : ℕ → Cat
  D n = Δ (suc n)

  W : ℕ → Cat
  W n = (D n ×c 𝕀) ×c D n

  p-outer : (n : ℕ) → Map (W n) (D n ×c 𝕀)
  p-outer n = π₁ (D n ×c 𝕀) (D n)

  p-y : (n : ℕ) → Map (W n) (D n)
  p-y n = π₂ (D n ×c 𝕀) (D n)

  p-σ : (n : ℕ) → Map (W n) (D n)
  p-σ n = comp (π₁ (D n) 𝕀) (p-outer n)

  p-t : (n : ℕ) → Map (W n) 𝕀
  p-t n = comp (π₂ (D n) 𝕀) (p-outer n)

  c20 : (n : ℕ) → Ob (Δ (suc n)) → Ord (suc n)
  c20 n = pr₁ (construction-20 (suc n))

  -- Retract Ord(suc n) → Ord n (left inverse of inl)
  deface : {n : ℕ} → Ord (suc n) → Ord n
  deface {zero}  _       = ⋆
  deface {suc n} (inl x) = x
  deface {suc n} (inr ⋆) = inr ⋆

  -- Top indicator: 1 iff y = top
  top-ind : {n : ℕ} → Ord (suc n) → 𝟚
  top-ind (inl _) = inl ⋆
  top-ind (inr ⋆) = inr ⋆

  -- Evaluate σ's monotone predicate at deface(y)
  σ-eval : (n : ℕ) → Ord (suc n) → Ord (suc n) → 𝟚
  σ-eval n σ_ord y_ord = pr₁ (monotone-ord-bwd n σ_ord) (deface y_ord)

  deface-mono : {n : ℕ} (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
    → _≤Ord_ {n} (deface x) (deface y)
  deface-mono {zero}  _       _       _ = ⋆
  deface-mono {suc n} (inl x) (inl y) le = le
  deface-mono {suc n} (inl x) (inr ⋆) le = any-≤Ord-top x
  deface-mono {suc n} (inr ⋆) (inl y) ()
  deface-mono {suc n} (inr ⋆) (inr ⋆) le = ⋆

  top-ind-mono : {n : ℕ} (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
    → top-ind x ≤𝟚 top-ind y
  top-ind-mono (inl _) _       _ = ⋆
  top-ind-mono (inr ⋆) (inl _) ()
  top-ind-mono (inr ⋆) (inr ⋆) _ = ⋆

  σ-eval-mono : (n : ℕ) (σ₁ σ₂ y₁ y₂ : Ord (suc n))
    → _≤Ord_ {suc n} σ₁ σ₂ → _≤Ord_ {suc n} y₁ y₂
    → σ-eval n σ₁ y₁ ≤𝟚 σ-eval n σ₂ y₂
  σ-eval-mono n σ₁ σ₂ y₁ y₂ leσ ley =
    ≤𝟚-trans
      (monotone-ord-bwd-pw n σ₁ σ₂ leσ (deface y₁))
      (pr₂ (monotone-ord-bwd n σ₂) (deface y₁) (deface y₂) (deface-mono y₁ y₂ ley))

  σ-eval-le-max : (a t : 𝟚) → a ≤𝟚 interp t a (inr ⋆)
  σ-eval-le-max a (inl ⋆) = ≤𝟚-refl a
  σ-eval-le-max a (inr ⋆) = any-≤𝟚-top a

ret-p : (n : ℕ) → Ob (W n) → 𝟚
ret-p n w =
  interp (top-ind y_ord) base (interp t_ord base (inr ⋆))
  where
    σ_ord = c20 n (comp (p-σ n) w)
    t_ord = pr₁ 𝕀-ob (comp (p-t n) w)
    y_ord = c20 n (comp (p-y n) w)
    base  = σ-eval n σ_ord y_ord

ret-p-mono : (n : ℕ) → is-monotone {W n} (ret-p n)
ret-p-mono n m = ≤𝟚-transport pd pc
  (interp-mono
    (top-ind (c20 n (dom m-y))) (top-ind (c20 n (cod m-y)))
    base₁ base₂
    (interp (pr₁ 𝕀-ob (dom m-t)) base₁ (inr ⋆))
    (interp (pr₁ 𝕀-ob (cod m-t)) base₂ (inr ⋆))
    (top-ind-mono (c20 n (dom m-y)) (c20 n (cod m-y)) (mor-to-ord-le (suc n) m-y))
    (σ-eval-mono n
      (c20 n (dom m-σ)) (c20 n (cod m-σ))
      (c20 n (dom m-y)) (c20 n (cod m-y))
      (mor-to-ord-le (suc n) m-σ) (mor-to-ord-le (suc n) m-y))
    (interp-mono
      (pr₁ 𝕀-ob (dom m-t)) (pr₁ 𝕀-ob (cod m-t))
      base₁ base₂ (inr ⋆) (inr ⋆)
      (𝕀-mor-order m-t)
      (σ-eval-mono n
        (c20 n (dom m-σ)) (c20 n (cod m-σ))
        (c20 n (dom m-y)) (c20 n (cod m-y))
        (mor-to-ord-le (suc n) m-σ) (mor-to-ord-le (suc n) m-y))
      (≤𝟚-refl (inr ⋆))
      (any-≤𝟚-top base₂))
    (σ-eval-le-max base₂ (pr₁ 𝕀-ob (cod m-t))))
  where
    m-σ = comp (p-σ n) m
    m-t = comp (p-t n) m
    m-y = comp (p-y n) m
    base₁ = σ-eval n (c20 n (dom m-σ)) (c20 n (dom m-y))
    base₂ = σ-eval n (c20 n (cod m-σ)) (c20 n (cod m-y))

    pd : interp (top-ind (c20 n (dom m-y))) base₁
           (interp (pr₁ 𝕀-ob (dom m-t)) base₁ (inr ⋆))
         ≡ ret-p n (dom m)
    pd = interp-cong
      (ap (top-ind ∘ c20 n) (dom-nat (p-y n) m))
      (ap (λ a → σ-eval n (c20 n a) (c20 n (dom m-y)))
          (dom-nat (p-σ n) m)
       ∙ ap (λ b → σ-eval n (c20 n (comp (p-σ n) (dom m))) (c20 n b))
          (dom-nat (p-y n) m))
      (interp-cong
        (ap (pr₁ 𝕀-ob) (dom-nat (p-t n) m))
        (ap (λ a → σ-eval n (c20 n a) (c20 n (dom m-y)))
            (dom-nat (p-σ n) m)
         ∙ ap (λ b → σ-eval n (c20 n (comp (p-σ n) (dom m))) (c20 n b))
            (dom-nat (p-y n) m))
        (refl (inr ⋆)))

    pc : interp (top-ind (c20 n (cod m-y))) base₂
           (interp (pr₁ 𝕀-ob (cod m-t)) base₂ (inr ⋆))
         ≡ ret-p n (cod m)
    pc = interp-cong
      (ap (top-ind ∘ c20 n) (cod-nat (p-y n) m))
      (ap (λ a → σ-eval n (c20 n a) (c20 n (cod m-y)))
          (cod-nat (p-σ n) m)
       ∙ ap (λ b → σ-eval n (c20 n (comp (p-σ n) (cod m))) (c20 n b))
          (cod-nat (p-y n) m))
      (interp-cong
        (ap (pr₁ 𝕀-ob) (cod-nat (p-t n) m))
        (ap (λ a → σ-eval n (c20 n a) (c20 n (cod m-y)))
            (cod-nat (p-σ n) m)
         ∙ ap (λ b → σ-eval n (c20 n (comp (p-σ n) (cod m))) (c20 n b))
            (cod-nat (p-y n) m))
        (refl (inr ⋆)))

ret-adj : (n : ℕ) → Map ((D n ×c 𝕀) ×c D n) 𝕀
ret-adj n = 𝕀-char-inverse ((D n ×c 𝕀) ×c D n) (ret-p n , ret-p-mono n)

ret : (n : ℕ) → Map (D n ×c 𝕀) (Δ (suc (suc n)))
ret n = equiv-inv (exp-equiv (D n) 𝕀 (D n ×c 𝕀)) (ret-adj n)

private
  XX : ℕ → Cat
  XX n = Δ (suc (suc n)) ×c D n

  gg : (n : ℕ) → Map (XX n) (W n)
  gg n = ⟨ comp (sect n) (π₁ (Δ (suc (suc n))) (D n)) ,
           π₂ (Δ (suc (suc n))) (D n) ⟩

  recon-top : (a b : 𝟚) → a ≤𝟚 b → interp b a (inr ⋆) ≡ b
  recon-top _ (inl ⋆) le = ≤𝟚-inl-forces-inl _ le
  recon-top _ (inr ⋆) _ = refl (inr ⋆)

  recon : {n : ℕ} (g : Ord (suc n) → 𝟚) (mono : is-monotone-Ord {suc n} g)
    (k : Ord (suc n))
    → interp (top-ind k) (g (inl (deface k)))
        (interp (g (inr ⋆)) (g (inl (deface k))) (inr ⋆))
      ≡ g k
  recon {zero} g _ (inl ⋆) = refl (g (inl ⋆))
  recon {suc _} g _ (inl x) = refl (g (inl x))
  recon {zero} g mono (inr ⋆) = recon-top (g (inl ⋆)) (g (inr ⋆))
    (mono (inl ⋆) (inr ⋆) ⋆)
  recon {suc n} g mono (inr ⋆) = recon-top (g (inl (inr ⋆))) (g (inr ⋆))
    (mono (inl (inr ⋆)) (inr ⋆) ⋆)

  σ-eval-expand : (n : ℕ) (σ : Ob (D n)) (o : Ord n)
    → pr₁ (monotone-ord-bwd n (c20 n σ)) o
      ≡ ob-to-𝟚 (ob-to-map (Δ n) 𝕀 σ) (equiv-inv (construction-20 n) o)
  σ-eval-expand n σ o =
    ap (λ w → pr₁ w o) (monotone-ord-linv n mt-σ)
    ∙ mt-fwd-eq n w-σ o
    where
      w-σ = 𝕀-char-comparison (Δ n) (ob-to-map (Δ n) 𝕀 σ)
      mt-σ = pr₁ (monotone-transfer n) w-σ

  -- eval-at-top simplification at an object
  eval-at-top-eval : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
    → comp (eval-at-top n) φ
      ≡ comp (ev (D n) 𝕀) ⟨ φ , top (suc n) ⟩
  eval-at-top-eval n φ =
    (comp-assoc (ev (D n) 𝕀)
      ⟨ idMap (Δ (suc (suc n))) , comp (top (suc n)) (! (Δ (suc (suc n)))) ⟩
      φ) ⁻¹
    ∙ ap (comp (ev (D n) 𝕀))
        (pair-nat (idMap (Δ (suc (suc n))))
                  (comp (top (suc n)) (! (Δ (suc (suc n)))))
                  φ
         ∙ pair-ap
             (comp-id-l φ)
             ((comp-assoc (top (suc n)) (! (Δ (suc (suc n)))) φ) ⁻¹
              ∙ ap (comp (top (suc n)))
                  (singletons-are-props (terminal 𝟏c)
                    (comp (! (Δ (suc (suc n)))) φ) (idMap 𝟏c))
              ∙ comp-id-r (top (suc n))))

  -- pre-face-n evaluation chain
  h₀-n : (n : ℕ) → Map (Δ (suc (suc n)) ×c Δ n) 𝕀
  h₀-n n = comp (ev (D n) 𝕀)
    ⟨ π₁ (Δ (suc (suc n))) (Δ n) , comp (face n) (π₂ (Δ (suc (suc n))) (Δ n)) ⟩

  pre-face-n-eval : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
    → ob-to-map (Δ n) 𝕀 (comp (pre-face-n n) φ)
      ≡ comp (h₀-n n) ⟨ comp φ (! (Δ n)) , idMap (Δ n) ⟩
  pre-face-n-eval n φ = exp-eval (Δ n) 𝕀 (Δ (suc (suc n))) (h₀-n n) φ

  h₀-n-simpl : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
    → comp (h₀-n n) ⟨ comp φ (! (Δ n)) , idMap (Δ n) ⟩
      ≡ comp (ev (D n) 𝕀) ⟨ comp φ (! (Δ n)) , face n ⟩
  h₀-n-simpl n φ =
    (comp-assoc (ev (D n) 𝕀)
      ⟨ π₁ (Δ (suc (suc n))) (Δ n) , comp (face n) (π₂ (Δ (suc (suc n))) (Δ n)) ⟩
      ⟨ comp φ (! (Δ n)) , idMap (Δ n) ⟩) ⁻¹
    ∙ ap (comp (ev (D n) 𝕀))
        (pair-nat (π₁ (Δ (suc (suc n))) (Δ n))
                  (comp (face n) (π₂ (Δ (suc (suc n))) (Δ n)))
                  ⟨ comp φ (! (Δ n)) , idMap (Δ n) ⟩
         ∙ pair-ap
             (pair-β₁ (comp φ (! (Δ n))) (idMap (Δ n)))
             ((comp-assoc (face n) (π₂ (Δ (suc (suc n))) (Δ n))
                 ⟨ comp φ (! (Δ n)) , idMap (Δ n) ⟩) ⁻¹
              ∙ ap (comp (face n)) (pair-β₂ (comp φ (! (Δ n))) (idMap (Δ n)))
              ∙ comp-id-r (face n)))

  pre-face-n-eval-simpl : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
    → ob-to-map (Δ n) 𝕀 (comp (pre-face-n n) φ)
      ≡ comp (ev (D n) 𝕀) ⟨ comp φ (! (Δ n)) , face n ⟩
  pre-face-n-eval-simpl n φ = pre-face-n-eval n φ ∙ h₀-n-simpl n φ

  -- pre-face pointwise evaluation
  pre-face-point : (n : ℕ) (φ : Ob (Δ (suc (suc n)))) (z : Ob (Δ n))
    → comp (ob-to-map (Δ n) 𝕀 (comp (pre-face-n n) φ)) z
      ≡ comp (ob-to-map (D n) 𝕀 φ) (comp (face n) z)
  pre-face-point n φ z =
    ap (λ f → comp f z) (pre-face-n-eval-simpl n φ)
    ∙ (comp-assoc (ev (D n) 𝕀) ⟨ comp φ (! (Δ n)) , face n ⟩ z) ⁻¹
    ∙ ap (comp (ev (D n) 𝕀))
        (pair-nat (comp φ (! (Δ n))) (face n) z
         ∙ pair-ap
             ((comp-assoc φ (! (Δ n)) z) ⁻¹
              ∙ ap (comp φ)
                  (singletons-are-props (terminal 𝟏c)
                    (comp (! (Δ n)) z) (idMap 𝟏c))
              ∙ comp-id-r φ)
             (refl (comp (face n) z)))
    ∙ (ev-point (D n) 𝕀 φ (comp (face n) z)) ⁻¹

  -- face/ordinal compatibility
  face-ord-compat : (n : ℕ) (k : Ord n)
    → comp (face n) (equiv-inv (construction-20 n) k)
      ≡ equiv-inv (construction-20 (suc n)) (inl k)
  face-ord-compat n k =
    (equiv-inv-linv (construction-20 (suc n)) (comp (face n) z)) ⁻¹
    ∙ ap (equiv-inv (construction-20 (suc n)))
        (c20-face-gen-u n z ∙ ap inl (equiv-inv-rinv (construction-20 n) k))
    where
      z = equiv-inv (construction-20 n) k

  -- c20-top inverse
  c20-top-inv : (n : ℕ)
    → equiv-inv (construction-20 (suc n)) (inr ⋆) ≡ top (suc n)
  c20-top-inv n =
    ap (equiv-inv (construction-20 (suc n))) (c20-top (suc n) ⁻¹)
    ∙ equiv-inv-linv (construction-20 (suc n)) (top (suc n))

  -- Projection lemmas for gg
  Xn : ℕ → Cat
  Xn n = Δ (suc (suc n))

  gg-outer : (n : ℕ) (w : Ob (XX n))
    → comp (p-outer n) (comp (gg n) w) ≡ comp (sect n) (comp (π₁ (Xn n) (D n)) w)
  gg-outer n w =
    comp-assoc (p-outer n) (gg n) w
    ∙ ap (λ g → comp g w) (pair-β₁ (comp (sect n) (π₁ (Xn n) (D n))) (π₂ (Xn n) (D n)))
    ∙ (comp-assoc (sect n) (π₁ (Xn n) (D n)) w) ⁻¹

  gg-p-y : (n : ℕ) (w : Ob (XX n))
    → comp (p-y n) (comp (gg n) w) ≡ comp (π₂ (Xn n) (D n)) w
  gg-p-y n w =
    comp-assoc (p-y n) (gg n) w
    ∙ ap (λ g → comp g w) (pair-β₂ (comp (sect n) (π₁ (Xn n) (D n))) (π₂ (Xn n) (D n)))

  gg-p-σ : (n : ℕ) (w : Ob (XX n))
    → comp (p-σ n) (comp (gg n) w) ≡ comp (pre-face-n n) (comp (π₁ (Xn n) (D n)) w)
  gg-p-σ n w =
    (comp-assoc (π₁ (D n) 𝕀) (p-outer n) (comp (gg n) w)) ⁻¹
    ∙ ap (comp (π₁ (D n) 𝕀)) (gg-outer n w)
    ∙ comp-assoc (π₁ (D n) 𝕀) (sect n) (comp (π₁ (Xn n) (D n)) w)
    ∙ ap (λ g → comp g (comp (π₁ (Xn n) (D n)) w))
        (pair-β₁ (pre-face-n n) (eval-at-top n))

  gg-p-t : (n : ℕ) (w : Ob (XX n))
    → comp (p-t n) (comp (gg n) w) ≡ comp (eval-at-top n) (comp (π₁ (Xn n) (D n)) w)
  gg-p-t n w =
    (comp-assoc (π₂ (D n) 𝕀) (p-outer n) (comp (gg n) w)) ⁻¹
    ∙ ap (comp (π₂ (D n) 𝕀)) (gg-outer n w)
    ∙ comp-assoc (π₂ (D n) 𝕀) (sect n) (comp (π₁ (Xn n) (D n)) w)
    ∙ ap (λ g → comp g (comp (π₁ (Xn n) (D n)) w))
        (pair-β₂ (pre-face-n n) (eval-at-top n))

  -- The face part
  face-part : (n : ℕ) (φ : Ob (Δ (suc (suc n)))) (y : Ob (D n))
    → σ-eval n (c20 n (comp (pre-face-n n) φ)) (c20 n y)
      ≡ pr₁ (monotone-ord-bwd (suc n) (c20 (suc n) φ)) (inl (deface (c20 n y)))
  face-part n φ y =
    σ-eval-expand n (comp (pre-face-n n) φ) (deface (c20 n y))
    ∙ ap (pr₁ 𝕀-ob) (pre-face-point n φ z)
    ∙ ap (ob-to-𝟚 (ob-to-map (D n) 𝕀 φ)) (face-ord-compat n (deface (c20 n y)))
    ∙ (σ-eval-expand (suc n) φ (inl (deface (c20 n y)))) ⁻¹
    where
      z = equiv-inv (construction-20 n) (deface (c20 n y))

  -- The top part
  top-part : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
    → pr₁ 𝕀-ob (comp (eval-at-top n) φ)
      ≡ pr₁ (monotone-ord-bwd (suc n) (c20 (suc n) φ)) (inr ⋆)
  top-part n φ =
    ap (pr₁ 𝕀-ob) (eval-at-top-eval n φ)
    ∙ ap (pr₁ 𝕀-ob) ((ev-point (D n) 𝕀 φ (top (suc n))) ⁻¹)
    ∙ ap (ob-to-𝟚 (ob-to-map (D n) 𝕀 φ)) ((c20-top-inv n) ⁻¹)
    ∙ (σ-eval-expand (suc n) φ (inr ⋆)) ⁻¹

  -- RHS simplification: ob-to-2 (ev ...) w = g (c20 n y)
  rhs-simp : (n : ℕ) (φ : Ob (Δ (suc (suc n)))) (y : Ob (D n))
    → pr₁ (monotone-ord-bwd (suc n) (c20 (suc n) φ)) (c20 n y)
      ≡ ob-to-𝟚 (ob-to-map (D n) 𝕀 φ) y
  rhs-simp n φ y =
    σ-eval-expand (suc n) φ (c20 n y)
    ∙ ap (ob-to-𝟚 (ob-to-map (D n) 𝕀 φ)) (equiv-inv-linv (construction-20 (suc n)) y)

  rhs-ev : (n : ℕ) (w : Ob (XX n))
    → ob-to-𝟚 (ob-to-map (D n) 𝕀 (comp (π₁ (Xn n) (D n)) w))
        (comp (π₂ (Xn n) (D n)) w)
      ≡ ob-to-𝟚 (ev (D n) 𝕀) w
  rhs-ev n w =
    ap (pr₁ 𝕀-ob) (ev-point (D n) 𝕀 (comp (π₁ (Xn n) (D n)) w) (comp (π₂ (Xn n) (D n)) w))
    ∙ ap (λ u → pr₁ 𝕀-ob (comp (ev (D n) 𝕀) u)) (pair-η w)

  -- σ-eval congruence helper
  σ-eval-cong : {n : ℕ} {a₁ a₂ : Ord (suc n)} {b₁ b₂ : Ord (suc n)}
    → a₁ ≡ a₂ → b₁ ≡ b₂ → σ-eval n a₁ b₁ ≡ σ-eval n a₂ b₂
  σ-eval-cong (refl _) (refl _) = refl _

  -- Core claim
  core : (n : ℕ) (w : Ob (XX n))
    → ret-p n (comp (gg n) w) ≡ ob-to-𝟚 (ev (D n) 𝕀) w
  core n w =
    interp-cong
      (ap (top-ind ∘ c20 n) (gg-p-y n w))
      (σ-eval-cong
        (ap (c20 n) (gg-p-σ n w))
        (ap (c20 n) (gg-p-y n w)))
      (interp-cong
        (ap (pr₁ 𝕀-ob) (gg-p-t n w))
        (σ-eval-cong
          (ap (c20 n) (gg-p-σ n w))
          (ap (c20 n) (gg-p-y n w)))
        (refl (inr ⋆)))
    ∙ interp-cong
        (refl (top-ind (c20 n y)))
        (face-part n φ y)
        (interp-cong (top-part n φ) (face-part n φ y) (refl (inr ⋆)))
    ∙ recon g (pr₂ (monotone-ord-bwd (suc n) (c20 (suc n) φ))) (c20 n y)
    ∙ rhs-simp n φ y
    ∙ rhs-ev n w
    where
      φ = comp (π₁ (Xn n) (D n)) w
      y = comp (π₂ (Xn n) (D n)) w
      g = pr₁ (monotone-ord-bwd (suc n) (c20 (suc n) φ))

  -- LHS step: ob-to-2 (comp (ret-adj n) (gg n)) w = ret-p n (comp (gg n) w)
  lhs-step : (n : ℕ) (w : Ob (XX n))
    → ob-to-𝟚 (comp (ret-adj n) (gg n)) w ≡ ret-p n (comp (gg n) w)
  lhs-step n w =
    ap (pr₁ 𝕀-ob) ((comp-assoc (ret-adj n) (gg n) w) ⁻¹)
    ∙ 𝕀-char-ob-to-𝟚 (W n) (ret-p n , ret-p-mono n) (comp (gg n) w)


------------------------------------------------------------------------
-- Round-trip: comp (ret n) (sect n) ≡ idMap (Δ (suc (suc n)))
--
-- Strategy: use equiv-inj with exp-comparison to reduce to showing
-- the uncurried versions agree.  The LHS uncurries (via exp-comp-nat
-- and equiv-inv-rinv) to  comp (ret-adj n) ⟨ sect∘π₁, π₂ ⟩.
-- The RHS uncurries to  ev Dn 𝕀.
-- The remaining claim (ret-sect-key) is the core mathematical content.
------------------------------------------------------------------------

ret-sect-key : (n : ℕ) →
  comp (ret-adj n)
    ⟨ comp (sect n) (π₁ (Δ (suc (suc n))) (Δ (suc n))) ,
      π₂ (Δ (suc (suc n))) (Δ (suc n)) ⟩
  ≡ ev (Δ (suc n)) 𝕀
ret-sect-key n =
  equiv-inj (𝕀-char-comparison (XX n)) (pr₂ (𝕀-char (XX n)))
    (to-Σ-≡ (funext (λ w → lhs-step n w ∙ core n w) ,
      is-monotone-is-prop (ob-to-𝟚 (ev (D n) 𝕀)) _ _))

ret-sect : (n : ℕ) → comp (ret n) (sect n) ≡ idMap (Δ (suc (suc n)))
ret-sect n = equiv-inj (exp-comparison Dn 𝕀 X) (exp-is-equiv Dn 𝕀 X)
  (lhs ∙ ret-sect-key n ∙ rhs ⁻¹)
  where
    Dn = Δ (suc n)
    X  = Δ (suc (suc n))

    lhs : exp-comparison Dn 𝕀 X (comp (ret n) (sect n))
        ≡ comp (ret-adj n) ⟨ comp (sect n) (π₁ X Dn) , π₂ X Dn ⟩
    lhs = exp-comp-nat (ret n) (sect n)
        ∙ ap (λ h → comp h ⟨ comp (sect n) (π₁ X Dn) , π₂ X Dn ⟩)
             (equiv-inv-rinv (exp-equiv Dn 𝕀 (Dn ×c 𝕀)) (ret-adj n))

    pair-id : ⟨ π₁ X Dn , π₂ X Dn ⟩ ≡ idMap (X ×c Dn)
    pair-id = pair-ap ((comp-id-r (π₁ X Dn)) ⁻¹) ((comp-id-r (π₂ X Dn)) ⁻¹)
            ∙ pair-η (idMap (X ×c Dn))

    rhs : exp-comparison Dn 𝕀 X (idMap X) ≡ ev Dn 𝕀
    rhs = ap (comp (ev Dn 𝕀))
            (pair-ap (comp-id-l (π₁ X Dn)) (refl _) ∙ pair-id)
          ∙ comp-id-r (ev Dn 𝕀)

------------------------------------------------------------------------
-- Public re-exports of private lemmas needed by Scratch-face-sect
------------------------------------------------------------------------

-- face-part: relates bwd of pfn at level n to bwd at level suc n
face-part-pub : (n : ℕ) (φ : Ob (Δ (suc (suc n)))) (o : Ord n)
  → pr₁ (monotone-ord-bwd n (pr₁ (construction-20 (suc n)) (comp (pre-face-n n) φ))) o
    ≡ pr₁ (monotone-ord-bwd (suc n) (pr₁ (construction-20 (suc (suc n))) φ)) (inl o)
face-part-pub n φ o =
  σ-eval-expand n (comp (pre-face-n n) φ) o
  ∙ ap (pr₁ 𝕀-ob) (pre-face-point n φ z)
  ∙ ap (ob-to-𝟚 (ob-to-map (D n) 𝕀 φ)) (face-ord-compat n o)
  ∙ (σ-eval-expand (suc n) φ (inl o)) ⁻¹
  where
    z = equiv-inv (construction-20 n) o

------------------------------------------------------------------------
-- Public exports for face-ret-compat proof
------------------------------------------------------------------------

-- Private helper re-exports
ret-p-c20 : (n : ℕ) → Ob (Δ (suc n)) → Ord (suc n)
ret-p-c20 = c20

ret-p-deface : {n : ℕ} → Ord (suc n) → Ord n
ret-p-deface = deface

ret-p-top-ind : {n : ℕ} → Ord (suc n) → 𝟚
ret-p-top-ind = top-ind

ret-p-σ-eval : (n : ℕ) → Ord (suc n) → Ord (suc n) → 𝟚
ret-p-σ-eval = σ-eval

-- σ-eval in terms of face-ord and deface
σ-eval-as-face-ord : (n : ℕ) (v : Ord n) (k : Ord (suc n))
  → σ-eval n (inl v) k ≡ face-ord n v (deface k)
σ-eval-as-face-ord n v k = refl _

-- Expand ret-p at a specific pairing ⟨ ⟨ σ , t ⟩ , y ⟩
ret-p-expand : (n : ℕ) (σ : Ob (D n)) (t : Ob 𝕀) (y : Ob (D n))
  → ret-p n ⟨ ⟨ σ , t ⟩ , y ⟩
    ≡ interp (top-ind (c20 n y))
        (σ-eval n (c20 n σ) (c20 n y))
        (interp (pr₁ 𝕀-ob t) (σ-eval n (c20 n σ) (c20 n y)) (inr ⋆))
ret-p-expand n σ t y =
  interp-cong
    (ap (top-ind ∘ c20 n) py-eq)
    (σ-eval-cong (ap (c20 n) pσ-eq) (ap (c20 n) py-eq))
    (interp-cong
      (ap (pr₁ 𝕀-ob) pt-eq)
      (σ-eval-cong (ap (c20 n) pσ-eq) (ap (c20 n) py-eq))
      (refl (inr ⋆)))
  where
    w = ⟨ ⟨ σ , t ⟩ , y ⟩
    pσ-eq : comp (p-σ n) w ≡ σ
    pσ-eq = (comp-assoc (π₁ (D n) 𝕀) (π₁ (D n ×c 𝕀) (D n)) w) ⁻¹
           ∙ ap (comp (π₁ (D n) 𝕀)) (pair-β₁ ⟨ σ , t ⟩ y)
           ∙ pair-β₁ σ t
    pt-eq : comp (p-t n) w ≡ t
    pt-eq = (comp-assoc (π₂ (D n) 𝕀) (π₁ (D n ×c 𝕀) (D n)) w) ⁻¹
           ∙ ap (comp (π₂ (D n) 𝕀)) (pair-β₁ ⟨ σ , t ⟩ y)
           ∙ pair-β₂ σ t
    py-eq : comp (p-y n) w ≡ y
    py-eq = pair-β₂ ⟨ σ , t ⟩ y

-- Recon: reconstruction of monotone function from lower + top parts
recon-pub : {n : ℕ} (g : Ord (suc n) → 𝟚) (mono : is-monotone-Ord {suc n} g)
  (k : Ord (suc n))
  → interp (top-ind k) (g (inl (deface k)))
      (interp (g (inr ⋆)) (g (inl (deface k))) (inr ⋆))
    ≡ g k
recon-pub = recon

-- Top part: relates eval-at-top to bwd at next level
top-part-pub : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
  → pr₁ 𝕀-ob (comp (eval-at-top n) φ)
    ≡ pr₁ (monotone-ord-bwd (suc n) (pr₁ (construction-20 (suc (suc n))) φ)) (inr ⋆)
top-part-pub = top-part

-- σ-eval-expand: relates ordinal computation to map evaluation
σ-eval-expand-pub : (n : ℕ) (σ : Ob (D n)) (o : Ord n)
  → pr₁ (monotone-ord-bwd n (c20 n σ)) o
    ≡ ob-to-𝟚 (ob-to-map (Δ n) 𝕀 σ) (equiv-inv (construction-20 n) o)
σ-eval-expand-pub = σ-eval-expand
