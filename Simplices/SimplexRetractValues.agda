{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26, GEOMETRIC LAYER — the vertex-value bridge (handoff §2).
--
-- Connects the geometric maps `sect`/`pre-face-n`/`eval-at-top` to their
-- object (vertex) actions, expressed through `construction-20`
-- (`Ob (Δ n) ≃ Ord n`) and the monotone-function semantics
-- (`monotone-ord-bwd`).  These are the object-level value lemmas that the
-- square-morphism commutations of `retract-SSk` consume (after `ipe`
-- reduces each to two projections and `posetal-eq-objects` reduces each
-- projection to an equation on objects).
--
-- The hard arithmetic is already packaged in `SimplexRetract` as
-- `top-part-pub` (eval-at-top's monotone value) and `face-part-pub`
-- (pre-face-n's monotone value); here we specialise them at the named
-- vertices `top`, and re-export the immediate `sect` projections.
------------------------------------------------------------------------

module Simplices.SimplexRetractValues where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks
open import Category.Exponentials
open import Interval.Interval
open import Simplices.LastEdge using (ord-top; bwd-top-const; last-edge; dom-last-edge;
  edge-cod; c20-inv-top)
open import Simplices.FaceTop using (top; c20-top)
open import Simplices.FaceMap using (face)
open import Category.Product using (injl; injr)
open import Interval.OrdComb using (sn2-pr1; sn2-snd; restrict; ord-suc-top; sn2-pr1-suc;
  sn2-snd-top; sn2-snd-face;
  deface; top-ind; sval; thr-pred; thr-mono; thr-ord)
open import Category.ExpEval using (exp-eval)
open import Posetal.Posetal using (posetal-eq-objects; Delta-posetal)
open import Simplices.SimplexRetract

------------------------------------------------------------------------
-- Abbreviation: the vertex coordinate of Δ n.
------------------------------------------------------------------------

c20 : (n : ℕ) → Ob (Δ n) → Ord n
c20 n = pr₁ (construction-20 n)

c20-inj : (n : ℕ) {x y : Ob (Δ n)} → c20 n x ≡ c20 n y → x ≡ y
c20-inj n = equiv-inj (c20 n) (pr₂ (construction-20 n))

𝕀ob-inj : {x y : Ob 𝕀} → pr₁ 𝕀-ob x ≡ pr₁ 𝕀-ob y → x ≡ y
𝕀ob-inj = equiv-inj (pr₁ 𝕀-ob) (pr₂ 𝕀-ob)

------------------------------------------------------------------------
-- The two projections of `sect n = ⟨ pre-face-n n , eval-at-top n ⟩`.
-- (injl = π₁ (Δ (suc n)) 𝕀 ; injr = π₂ (Δ (suc n)) 𝕀.)
------------------------------------------------------------------------

sect-π₁ : (n : ℕ) → comp injl (sect n) ≡ pre-face-n n
sect-π₁ n = pair-β₁ (pre-face-n n) (eval-at-top n)

sect-π₂ : (n : ℕ) → comp injr (sect n) ≡ eval-at-top n
sect-π₂ n = pair-β₂ (pre-face-n n) (eval-at-top n)

------------------------------------------------------------------------
-- Vertex action of `eval-at-top` at the TOP vertex: eval-at-top@top = 𝕀₁.
--
--   𝕀-ob (eval-at-top n (top (2+n)))
--     = bwd (suc n) (c20 (2+n) (top (2+n))) (inr ⋆)   [top-part-pub]
--     = bwd (suc n) (inr ⋆)               (inr ⋆)     [c20-top]
--     = inr ⋆                                         [bwd-top-const]
--     = 𝕀-ob 𝕀₁
------------------------------------------------------------------------

eval-at-top-top : (n : ℕ)
  → comp (eval-at-top n) (top (suc (suc n))) ≡ 𝕀₁
eval-at-top-top n = 𝕀ob-inj
  ( top-part-pub n (top (suc (suc n)))
  ∙ ap (λ d → pr₁ (monotone-ord-bwd (suc n) d) (inr ⋆)) (c20-top (suc (suc n)))
  ∙ bwd-top-const (suc n) (inr ⋆)
  ∙ (equiv-inv-rinv 𝕀-ob (inr ⋆)) ⁻¹ )

------------------------------------------------------------------------
-- Vertex action of `pre-face-n` at the TOP vertex: pre-face-n@top = top.
--
-- Show c20 (suc n) (pre-face-n n (top (2+n))) ≡ inr ⋆ = c20 (suc n) (top).
-- The monotone function of pre-face-n@top is constantly (inr ⋆):
--   bwd n (c20 (pre-face-n@top)) o
--     = bwd (suc n) (c20 (top (2+n))) (inl o)   [face-part-pub]
--     = bwd (suc n) (inr ⋆)         (inl o)     [c20-top]
--     = inr ⋆                                   [bwd-top-const]
-- so it equals bwd n (inr ⋆); applying fwd (monotone-ord-rinv) gives inr ⋆.
------------------------------------------------------------------------

pre-face-top : (n : ℕ)
  → comp (pre-face-n n) (top (suc (suc n))) ≡ top (suc n)
pre-face-top n = c20-inj (suc n) (c-is-top ∙ (c20-top (suc n)) ⁻¹)
  where
  c : Ord (suc n)
  c = c20 (suc n) (comp (pre-face-n n) (top (suc (suc n))))

  bwd-eq : monotone-ord-bwd n c ≡ monotone-ord-bwd n (inr ⋆)
  bwd-eq = to-Σ-≡
    ( funext (λ o →
        face-part-pub n (top (suc (suc n))) o
        ∙ ap (λ d → pr₁ (monotone-ord-bwd (suc n) d) (inl o)) (c20-top (suc (suc n)))
        ∙ bwd-top-const (suc n) (inl o)
        ∙ (bwd-top-const n o) ⁻¹)
    , is-monotone-Ord-is-prop _ _ _ )

  c-is-top : c ≡ inr ⋆
  c-is-top =
      (monotone-ord-rinv n c) ⁻¹
    ∙ ap (monotone-ord-fwd n) bwd-eq
    ∙ monotone-ord-rinv n (inr ⋆)

------------------------------------------------------------------------
-- The GENERAL vertex actions (Rocq `ΔSnto_injl` / `ΔSnto_injr`):
--   c20  (pre-face-n n φ)      = sn2-pr1 n (c20 φ)
--   𝕀-ob (eval-at-top n φ)     = sn2-snd n (c20 φ)
-- These are the object actions of the two `sect` projections, expressed
-- through the OrdComb section bijection.  They bridge the simplex maps to
-- pure ordinal combinatorics, so the `posetal-eq-objects`-reduced
-- commutations become ordinal `refl`s once OrdComb's `sn2-*` identities
-- (the dni/lastedge projection lemmas) are available.
------------------------------------------------------------------------

-- pre-face-n's monotone function is the inl-restriction of φ's (face-part-pub);
-- reading back the ordinal (fwd ∘ bwd = id) gives sn2-pr1.
pre-face-val : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
  → c20 (suc n) (comp (pre-face-n n) φ) ≡ sn2-pr1 n (c20 (suc (suc n)) φ)
pre-face-val n φ =
    (monotone-ord-rinv n d) ⁻¹
  ∙ ap (monotone-ord-fwd n) bwd-eq
  where
  d : Ord (suc n)
  d = c20 (suc n) (comp (pre-face-n n) φ)

  bwd-eq : monotone-ord-bwd n d
         ≡ restrict (monotone-ord-bwd (suc n) (c20 (suc (suc n)) φ))
  bwd-eq = to-Σ-≡
    ( funext (λ o → face-part-pub n φ o)
    , is-monotone-Ord-is-prop _ _ _ )

-- eval-at-top's 𝟚-value is φ's monotone function at the top vertex: that is
-- exactly `sn2-snd` (definitionally), so this is `top-part-pub` restated.
eval-val : (n : ℕ) (φ : Ob (Δ (suc (suc n))))
  → pr₁ 𝕀-ob (comp (eval-at-top n) φ) ≡ sn2-snd n (c20 (suc (suc n)) φ)
eval-val n φ = top-part-pub n φ

------------------------------------------------------------------------
-- The `last-edge` vertex action (Rocq `lastedge_val`).  `last-edge n` is
-- the 1-simplex 𝕀 → Δ(suc n) from `dni_lastelement lastelement` to the top
-- vertex; on objects it sends 𝕀₀ ↦ inl(ord-top n) and 𝕀₁ ↦ inr ⋆.  Since
-- `Ob 𝕀 ≃ 𝟚`, a general `x` is `𝕀₀`/`𝕀₁` according to `𝕀-ob x`, so we case
-- on it (no enumeration of `Ob 𝕀` needed) and read off `dom`/`cod`.
------------------------------------------------------------------------

lastedge-ord : (n : ℕ) → 𝟚 → Ord (suc n)
lastedge-ord n (inl ⋆) = inl (ord-top n)
lastedge-ord n (inr ⋆) = inr ⋆

-- dom/cod c20 values: comp (last-edge n) 𝕀₀ = dom, comp (last-edge n) 𝕀₁ = cod.
last-edge-dom-c20 : (n : ℕ) → c20 (suc n) (comp (last-edge n) 𝕀₀) ≡ inl (ord-top n)
last-edge-dom-c20 n =
    ap (c20 (suc n)) (dom-last-edge n)
  ∙ equiv-inv-rinv (construction-20 (suc n)) (inl (ord-top n))

last-edge-cod-c20 : (n : ℕ) → c20 (suc n) (comp (last-edge n) 𝕀₁) ≡ inr ⋆
last-edge-cod-c20 n =
    ap (c20 (suc n)) (edge-cod n ∙ (c20-inv-top n) ⁻¹)
  ∙ equiv-inv-rinv (construction-20 (suc n)) (inr ⋆)

last-edge-c20-aux : (n : ℕ) (x : Ob 𝕀) (b : 𝟚) → pr₁ 𝕀-ob x ≡ b
  → c20 (suc n) (comp (last-edge n) x) ≡ lastedge-ord n b
last-edge-c20-aux n x (inl ⋆) eq =
    ap (λ z → c20 (suc n) (comp (last-edge n) z)) x-is-𝕀₀
  ∙ last-edge-dom-c20 n
  where
  x-is-𝕀₀ : x ≡ 𝕀₀
  x-is-𝕀₀ = (equiv-inv-linv 𝕀-ob x) ⁻¹ ∙ ap (equiv-inv 𝕀-ob) eq
last-edge-c20-aux n x (inr ⋆) eq =
    ap (λ z → c20 (suc n) (comp (last-edge n) z)) x-is-𝕀₁
  ∙ last-edge-cod-c20 n
  where
  x-is-𝕀₁ : x ≡ 𝕀₁
  x-is-𝕀₁ = (equiv-inv-linv 𝕀-ob x) ⁻¹ ∙ ap (equiv-inv 𝕀-ob) eq

last-edge-c20 : (n : ℕ) (x : Ob 𝕀)
  → c20 (suc n) (comp (last-edge n) x) ≡ lastedge-ord n (pr₁ 𝕀-ob x)
last-edge-c20 n x = last-edge-c20-aux n x (pr₁ 𝕀-ob x) (refl _)

------------------------------------------------------------------------
-- The two ordinal identities for `smr-s` (Rocq `Sn2inv_dnifirst/last` on
-- the `lastedge_fn` values): `pre-face-n` and `eval-at-top` post-composed
-- with `lastedge` collapse on the two `lastedge-ord` values.
------------------------------------------------------------------------

-- lastedge-ord(suc k) b ≡ sn2-pr1(suc k) (lastedge-ord(suc(suc k)) b)
lastedge-sn2-pr1 : (k : ℕ) (b : 𝟚)
  → lastedge-ord (suc k) b ≡ sn2-pr1 (suc k) (lastedge-ord (suc (suc k)) b)
lastedge-sn2-pr1 k (inl ⋆) =
  ( ap (sn2-pr1 (suc k)) ((ap inl (ord-suc-top k)) ⁻¹)
  ∙ sn2-pr1-suc (suc k) (inl (inr ⋆)) ) ⁻¹
lastedge-sn2-pr1 k (inr ⋆) =
  ( ap (sn2-pr1 (suc k)) ((ord-suc-top (suc k)) ⁻¹)
  ∙ sn2-pr1-suc (suc k) (inr ⋆) ) ⁻¹

-- inr ⋆ ≡ sn2-snd(suc k) (lastedge-ord(suc(suc k)) b)   (eval-at-top@lastedge = 1)
lastedge-sn2-snd : (k : ℕ) (b : 𝟚)
  → inr ⋆ ≡ sn2-snd (suc k) (lastedge-ord (suc (suc k)) b)
lastedge-sn2-snd k (inl ⋆) =
  ( (sn2-snd-face k (inr ⋆)) ⁻¹ ∙ sn2-snd-top k ) ⁻¹
lastedge-sn2-snd k (inr ⋆) =
  (sn2-snd-top (suc k)) ⁻¹

------------------------------------------------------------------------
-- The vertex-functor semantics layer.
--
-- `vob n f` is the object/vertex action of a map `f : X → Δ n`, read as
-- an ordinal-valued function `Ob X → Ord n`.  Because Δ n is posetal,
-- a map into Δ n is DETERMINED by `vob` (`vob-ext`), and `vob` of a
-- precomposite is `vob` reindexed (`vob-pre`).  Together with the value
-- dictionary (`c20-face-gen-u`, `last-edge-c20`, `c20-top`, and the
-- `ret` value `ret-c20` below) this turns every equation of simplex
-- maps into a finite-ordinal identity.
------------------------------------------------------------------------

vob : (n : ℕ) {X : Cat} → Map X (Δ n) → Ob X → Ord n
vob n f x = c20 n (comp f x)

vob-ext : {X : Cat} (n : ℕ) {f g : Map X (Δ n)}
        → ((x : Ob X) → vob n f x ≡ vob n g x) → f ≡ g
vob-ext n h = posetal-eq-objects (Delta-posetal n) (λ x → c20-inj n (h x))

vob-pre : (n : ℕ) {X Y : Cat} (f : Map Y (Δ n)) (h : Map X Y) (x : Ob X)
        → vob n (comp f h) x ≡ vob n f (comp h x)
vob-pre n f h x = ap (c20 n) (composeA f h x)

------------------------------------------------------------------------
-- Bridges from SimplexRetract's private `top-ind`/`σ-eval`/`deface`
-- (re-exported as `ret-p-*`) to the Cat-free OrdComb copies.
------------------------------------------------------------------------

df-bridge : {m : ℕ} (o' : Ord (suc m)) → ret-p-deface o' ≡ deface o'
df-bridge {zero}  o'      = refl _
df-bridge {suc m} (inl x) = refl _
df-bridge {suc m} (inr ⋆) = refl _

ti-bridge : {m : ℕ} (x : Ord (suc m)) → ret-p-top-ind x ≡ top-ind x
ti-bridge (inl _) = refl _
ti-bridge (inr ⋆) = refl _

se-bridge : (m : ℕ) (a' o' : Ord (suc m)) → ret-p-σ-eval m a' o' ≡ sval m a' o'
se-bridge m a' o' = ap (pr₁ (monotone-ord-bwd m a')) (df-bridge o')

-- `ret-p` at a pairing reads as the OrdComb predicate `thr-pred`.
ret-p-thr : (n : ℕ) (σ : Ob (Δ (suc n))) (t : Ob 𝕀) (point : Ob (Δ (suc n)))
  → ret-p n ⟨ ⟨ σ , t ⟩ , point ⟩
    ≡ thr-pred n (c20 (suc n) σ) (pr₁ 𝕀-ob t) (c20 (suc n) point)
ret-p-thr n σ t point =
    ret-p-expand n σ t point
  ∙ interp-cong
      (ti-bridge (c20 (suc n) point))
      (se-bridge n (c20 (suc n) σ) (c20 (suc n) point))
      (interp-cong (refl (pr₁ 𝕀-ob t))
        (se-bridge n (c20 (suc n) σ) (c20 (suc n) point))
        (refl (inr ⋆)))

------------------------------------------------------------------------
-- The vertex action of `ret` (handoff §1; Rocq `retr_thr_val`):
--   c20 (ret n w) = thr-ord n (Δ-coord of w) (𝕀-coord of w).
-- The single deepest bridge; feeds all three ret-side commutations.
------------------------------------------------------------------------

ret-c20 : (n : ℕ) (w : Ob (Δ (suc n) ×c 𝕀))
  → c20 (suc (suc n)) (comp (ret n) w)
  ≡ thr-ord n (c20 (suc n) (comp (π₁ (Δ (suc n)) 𝕀) w))
              (pr₁ 𝕀-ob (comp (π₂ (Δ (suc n)) 𝕀) w))
ret-c20 n w =
    (monotone-ord-rinv (suc n) (c20 (suc (suc n)) ψ)) ⁻¹
  ∙ ap (monotone-ord-fwd (suc n)) bwd-eq
  where
  Dn = Δ (suc n)
  σ  = comp (π₁ Dn 𝕀) w
  t  = comp (π₂ Dn 𝕀) w
  a  = c20 (suc n) σ
  b  = pr₁ 𝕀-ob t
  ψ  = comp (ret n) w

  point-eq : (o : Ord (suc n))
    → pr₁ (monotone-ord-bwd (suc n) (c20 (suc (suc n)) ψ)) o ≡ thr-pred n a b o
  point-eq o =
      σ-eval-expand-pub (suc n) ψ o
    ∙ ap (λ f → pr₁ 𝕀-ob (comp f point))
        (exp-eval Dn 𝕀 (Dn ×c 𝕀) (ret-adj n) w)
    ∙ ap (pr₁ 𝕀-ob) (composeA (ret-adj n) PAIR point)
    ∙ ap (λ u → pr₁ 𝕀-ob (comp (ret-adj n) u)) pair-simp
    ∙ 𝕀-char-ob-to-𝟚 ((Dn ×c 𝕀) ×c Dn) (ret-p n , ret-p-mono n) ⟨ w , point ⟩
    ∙ ap (λ u → ret-p n ⟨ u , point ⟩) ((pair-η w) ⁻¹)
    ∙ ret-p-thr n σ t point
    ∙ ap (thr-pred n a b) (equiv-inv-rinv (construction-20 (suc n)) o)
    where
    point = equiv-inv (construction-20 (suc n)) o
    PAIR  = ⟨ comp w (! Dn) , idMap Dn ⟩
    left  : comp (comp w (! Dn)) point ≡ w
    left  = composeA w (! Dn) point
          ∙ ap (comp w) (singletons-are-props (terminal 𝟏c)
                          (comp (! Dn) point) (idMap 𝟏c))
          ∙ comp-id-r w
    pair-simp : comp PAIR point ≡ ⟨ w , point ⟩
    pair-simp = pair-nat (comp w (! Dn)) (idMap Dn) point
              ∙ pair-ap left (comp-id-l point)

  bwd-eq : monotone-ord-bwd (suc n) (c20 (suc (suc n)) ψ)
         ≡ (thr-pred n a b , thr-mono n a b)
  bwd-eq = to-Σ-≡ (funext point-eq , is-monotone-Ord-is-prop _ _ _)
