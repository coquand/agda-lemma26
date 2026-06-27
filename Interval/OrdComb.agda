{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26, STREAM A — the finite-ordinal combinatorics layer (handoff §1).
--
-- Pure combinatorics on `Ord` (no `Cat`), reusable and fast.  Mirrors the
-- Rocq `Sn2_to_SSn` / `Sn2_to_SSn_inv` retraction `⟦S(S n)⟧ ≅ ⟦S n⟧ × ⟦2⟧`
-- that underlies `sect` on objects (Main.v 3694).  Here the analogue is
-- expressed through the monotone-function semantics `monotone-ord-bwd`
-- (`Ord (suc n) ≃ MonotoneOrd n`), matching the Agda `sect` (whose vertex
-- action restricts/evaluates the monotone function), rather than the raw
-- `stn` recursion UniMath uses — the two are different (both valid)
-- retractions of the same poset.
--
--   sn2-pr1 c  = the ordinal of the monotone function of c restricted along
--                inl   (= the vertex action of `pre-face-n`)
--   sn2-snd c  = the value of that monotone function at the top vertex
--                (= the 𝟚-value of the vertex action of `eval-at-top`)
------------------------------------------------------------------------

module Interval.OrdComb where

open import Foundations.Spartan
open import Category.HigherCat using (𝟚)
open import Interval.Interval

------------------------------------------------------------------------
-- bwd at the top ordinal is constantly 1  (pure-ordinal version of
-- LastEdge.bwd-top-const; re-proved here to keep this module Cat-free).
------------------------------------------------------------------------

bwd-top : (n : ℕ) (x : Ord n)
  → pr₁ (monotone-ord-bwd n (inr ⋆)) x ≡ inr ⋆
bwd-top zero          ⋆       = refl (inr ⋆)
bwd-top (suc zero)    (inl ⋆) = refl (inr ⋆)
bwd-top (suc zero)    (inr ⋆) = refl (inr ⋆)
bwd-top (suc (suc n)) (inl x) = bwd-top (suc n) x
bwd-top (suc (suc n)) (inr ⋆) = refl (inr ⋆)

------------------------------------------------------------------------
-- Restriction of a monotone Ord(suc n)→𝟚 to Ord n along inl.
-- (The vertex map of `face n : Δ n → Δ (suc n)` is inl = dni_lastelement,
-- so precomposition restricts the monotone function along inl.)
------------------------------------------------------------------------

restrict : {n : ℕ} → MonotoneOrd (suc n) → MonotoneOrd n
restrict {n} (q , mono) =
  (λ o → q (inl o)) , (λ x y le → mono (inl x) (inl y) le)

------------------------------------------------------------------------
-- The two components of the section bijection on Ord, via the semantics.
------------------------------------------------------------------------

-- vertex action of `pre-face-n n` on Ord: restrict the monotone function,
-- then read back the ordinal.   sn2-pr1 : Ord(2+n) → Ord(1+n).
sn2-pr1 : (n : ℕ) → Ord (suc (suc n)) → Ord (suc n)
sn2-pr1 n c = monotone-ord-fwd n (restrict (monotone-ord-bwd (suc n) c))

-- 𝟚-value of the vertex action of `eval-at-top n`: the monotone function of
-- c evaluated at the top vertex.   sn2-snd : Ord(2+n) → 𝟚.
sn2-snd : (n : ℕ) → Ord (suc (suc n)) → 𝟚
sn2-snd n c = pr₁ (monotone-ord-bwd (suc n) c) (inr ⋆)

-- at the top ordinal the second component is 1 (Rocq `Sn2inv_last_pr2`).
sn2-snd-top : (n : ℕ) → sn2-snd n (inr ⋆) ≡ inr ⋆
sn2-snd-top n = bwd-top (suc n) (inr ⋆)

------------------------------------------------------------------------
-- `ord-unsuc` on `inl` (used to compute `bwd` of an `inl` ordinal).
------------------------------------------------------------------------

ord-unsuc-top : (n : ℕ) → ord-unsuc n (inr ⋆) ≡ inr (inr ⋆)
ord-unsuc-top zero    = refl _
ord-unsuc-top (suc n) = refl _

-- `ord-suc` fixes the top ordinal.
ord-suc-top : (n : ℕ) → ord-suc n (inr ⋆) ≡ inr ⋆
ord-suc-top zero    = refl _
ord-suc-top (suc n) = refl _

ord-unsuc-inl : (n : ℕ) (c : Ord (suc (suc n)))
  → ord-unsuc (suc n) (inl c) ≡ ord-unsuc-lift n (ord-unsuc n c)
ord-unsuc-inl n (inl y) = refl _
ord-unsuc-inl n (inr ⋆) = (ap (ord-unsuc-lift n) (ord-unsuc-top n)) ⁻¹

------------------------------------------------------------------------
-- `sn2-snd` commutes with the `inl` (dni_lastelement) face inclusion:
--   sn2-snd n c = sn2-snd (suc n) (inl c)     (Rocq `Sn2inv_dnilast_pr2`).
-- Both equal the indicator "c is not the bottom ordinal", read off the
-- monotone function's value at the top vertex.
------------------------------------------------------------------------

snd-inl-aux : (m : ℕ) (r : 𝟙 + Ord (suc m))
  → pr₁ (monotone-ord-bwd-aux m r) (inr ⋆)
  ≡ pr₁ (monotone-ord-bwd-aux (suc m) (ord-unsuc-lift m r)) (inr ⋆)
snd-inl-aux m (inl ⋆)  = refl (inl ⋆)
snd-inl-aux m (inr c') = refl (inr ⋆)

sn2-snd-face : (n : ℕ) (c : Ord (suc (suc n)))
  → sn2-snd n c ≡ sn2-snd (suc n) (inl c)
sn2-snd-face n c =
    snd-inl-aux n (ord-unsuc n c)
  ∙ (ap (λ r → pr₁ (monotone-ord-bwd-aux (suc n) r) (inr ⋆)) (ord-unsuc-inl n c)) ⁻¹

------------------------------------------------------------------------
-- The first component `sn2-pr1` commutes with the `inl` (dni_lastelement)
-- face inclusion (Rocq `Sn2inv_dnilast_pr1`): the residual identity for
-- the section-side `smb-s` commutation (other leg = `sn2-snd-face`).
--
-- Proof: `sn2-pr1 = fwd ∘ restrict ∘ bwd` collapses on the two ordinal
-- shapes.  `restrict` of `bwd-aux _ (inr c')` is `bwd c'` (its inl-part),
-- and `restrict` of `bwd-aux _ (inl ⋆)` is all-zeros, so:
--   sn2-pr1 n (ord-suc n c') = fwd(bwd c') = c'        [via ord-unsuc-suc]
--   sn2-pr1 n (ord-bot)      = fwd(all-zeros) = ord-bot [via ord-unsuc-bot]
-- Every `c` is `ord-bot` or `ord-suc c'` (ord-class-rinv); `inl` commutes
-- with `ord-suc`/`ord-bot` definitionally, so the two collapses match.
------------------------------------------------------------------------

-- restrict of `bwd-aux n (inr c')` is just `bwd n c'` (the inl-part).
restrict-inr : (n : ℕ) (c' : Ord (suc n))
  → restrict (monotone-ord-bwd-aux n (inr c')) ≡ monotone-ord-bwd n c'
restrict-inr n c' =
  to-Σ-≡ (refl _ , is-monotone-Ord-is-prop _ _ _)

-- sn2-pr1 of a successor is the predecessor.
sn2-pr1-suc : (n : ℕ) (c' : Ord (suc n))
  → sn2-pr1 n (ord-suc n c') ≡ c'
sn2-pr1-suc n c' =
    ap (λ r → monotone-ord-fwd n (restrict (monotone-ord-bwd-aux n r)))
       (ord-unsuc-suc n c')
  ∙ ap (monotone-ord-fwd n) (restrict-inr n c')
  ∙ monotone-ord-rinv n c'

-- sn2-pr1 of the bottom ordinal is the bottom ordinal.
sn2-pr1-bot : (n : ℕ) → sn2-pr1 n (ord-bot (suc n)) ≡ ord-bot n
sn2-pr1-bot n =
    ap (λ r → monotone-ord-fwd n (restrict (monotone-ord-bwd-aux n r)))
       (ord-unsuc-bot n)
  ∙ fwd-all-zeros n

-- the identity holding on the classified form of c.
sn2-pr1-inl-class : (n : ℕ) (r : 𝟙 + Ord (suc n))
  → inl (sn2-pr1 n (ord-from-class n r))
  ≡ sn2-pr1 (suc n) (inl (ord-from-class n r))
sn2-pr1-inl-class n (inl ⋆) =
    ap inl (sn2-pr1-bot n) ∙ (sn2-pr1-bot (suc n)) ⁻¹
sn2-pr1-inl-class n (inr c') =
    ap inl (sn2-pr1-suc n c') ∙ (sn2-pr1-suc (suc n) (inl c')) ⁻¹

sn2-pr1-inl : (n : ℕ) (c : Ord (suc (suc n)))
  → inl (sn2-pr1 n c) ≡ sn2-pr1 (suc n) (inl c)
sn2-pr1-inl n c =
  transport (λ z → inl (sn2-pr1 n z) ≡ sn2-pr1 (suc n) (inl z))
    (ord-class-rinv n c) (sn2-pr1-inl-class n (ord-unsuc n c))

------------------------------------------------------------------------
-- The vertex action of the RETRACTION `ret` as an explicit ordinal
-- function (handoff §2; Rocq `thr_fn`).  `ret n` collapses a vertex
-- (a , b) of Δ(suc n) ×c 𝕀 — a ∈ Ord(suc n), b ∈ 𝟚 — to a vertex of
-- Δ(suc(suc n)).  We give that vertex as `thr-ord n a b`, the `fwd` of
-- a monotone predicate `thr-pred n a b` on Ord(suc n), and prove the
-- two ordinal identities the square commutations need:
--   * `thr-dnilast` : inl (thr-ord n a b) ≡ thr-ord (suc n) (inl a) b
--   * `thr-nonbot`  : nbot n a ≡ inr ⋆ → thr-ord n a b ≡ ord-suc n a
-- These reduce the three ret-side commutations to pure combinatorics.
------------------------------------------------------------------------

-- The predicate building blocks (mirroring SimplexRetract's private
-- `deface`/`top-ind`/`σ-eval`, kept here Cat-free).
deface : {n : ℕ} → Ord (suc n) → Ord n
deface {zero}  _       = ⋆
deface {suc n} (inl x) = x
deface {suc n} (inr ⋆) = inr ⋆

top-ind : {n : ℕ} → Ord (suc n) → 𝟚
top-ind (inl _) = inl ⋆
top-ind (inr ⋆) = inr ⋆

-- `deface (inl o') = o'` (not definitional at an abstract level).
deface-inl : {n : ℕ} (o' : Ord n) → deface {n} (inl o') ≡ o'
deface-inl {zero}  ⋆  = refl _
deface-inl {suc m} o' = refl _

sval : (n : ℕ) → Ord (suc n) → Ord (suc n) → 𝟚
sval n a o = pr₁ (monotone-ord-bwd n a) (deface o)

-- interp i (inr ⋆) (inr ⋆) is always (inr ⋆).
interp-rr : (i : 𝟚) → interp i (inr ⋆) (inr ⋆) ≡ inr ⋆
interp-rr (inl ⋆) = refl _
interp-rr (inr ⋆) = refl _

-- The monotone predicate of `ret` at (a , b).
thr-pred : (n : ℕ) → Ord (suc n) → 𝟚 → Ord (suc n) → 𝟚
thr-pred n a b o =
  interp (top-ind o) (sval n a o) (interp b (sval n a o) (inr ⋆))

-- Monotonicity (a , b fixed; structurally simpler than `ret-p-mono`).
deface-mono : {n : ℕ} (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
            → _≤Ord_ {n} (deface x) (deface y)
deface-mono {zero}  _       _       _  = ⋆
deface-mono {suc n} (inl x) (inl y) le = le
deface-mono {suc n} (inl x) (inr ⋆) le = any-≤Ord-top x
deface-mono {suc n} (inr ⋆) (inl y) ()
deface-mono {suc n} (inr ⋆) (inr ⋆) le = ⋆

top-ind-mono : {n : ℕ} (x y : Ord (suc n)) → _≤Ord_ {suc n} x y
             → top-ind x ≤𝟚 top-ind y
top-ind-mono (inl _) _       _ = ⋆
top-ind-mono (inr ⋆) (inl _) ()
top-ind-mono (inr ⋆) (inr ⋆) _ = ⋆

sval-le-max : (a t : 𝟚) → a ≤𝟚 interp t a (inr ⋆)
sval-le-max a (inl ⋆) = ≤𝟚-refl a
sval-le-max a (inr ⋆) = any-≤𝟚-top a

thr-mono : (n : ℕ) (a : Ord (suc n)) (b : 𝟚)
         → is-monotone-Ord {suc n} (thr-pred n a b)
thr-mono n a b x y le =
  interp-mono (top-ind x) (top-ind y) (sval n a x) (sval n a y)
    (interp b (sval n a x) (inr ⋆)) (interp b (sval n a y) (inr ⋆))
    (top-ind-mono x y le)
    sxy
    (interp-mono b b (sval n a x) (sval n a y) (inr ⋆) (inr ⋆)
      (≤𝟚-refl b) sxy (≤𝟚-refl (inr ⋆)) (any-≤𝟚-top (sval n a y)))
    (sval-le-max (sval n a y) b)
  where
    sxy : sval n a x ≤𝟚 sval n a y
    sxy = pr₂ (monotone-ord-bwd n a) (deface x) (deface y) (deface-mono x y le)

thr-ord : (n : ℕ) → Ord (suc n) → 𝟚 → Ord (suc (suc n))
thr-ord n a b = monotone-ord-fwd (suc n) (thr-pred n a b , thr-mono n a b)

------------------------------------------------------------------------
-- The "ord-suc" branch: when the predicate is 1 at the top, fwd of it
-- is `ord-suc n a` (the predicate then equals bwd of ord-suc n a).
------------------------------------------------------------------------

thr-top : (n : ℕ) (a : Ord (suc n)) (b : 𝟚)
        → thr-pred n a b (inr ⋆) ≡ inr ⋆
        → thr-ord n a b ≡ ord-suc n a
thr-top n a b hyp =
    ap (monotone-ord-fwd (suc n)) pred-eq
  ∙ monotone-ord-rinv (suc n) (ord-suc n a)
  where
  pe : (o : Ord (suc n))
     → thr-pred n a b o ≡ pr₁ (monotone-ord-bwd-aux n (inr a)) o
  pe (inl o') = ap (pr₁ (monotone-ord-bwd n a)) (deface-inl o')
  pe (inr ⋆)  = hyp
  pred-eq : (thr-pred n a b , thr-mono n a b)
          ≡ monotone-ord-bwd (suc n) (ord-suc n a)
  pred-eq = to-Σ-≡
    ( funext (λ o → pe o
        ∙ (ap (λ r → pr₁ (monotone-ord-bwd-aux n r) o) (ord-unsuc-suc n a)) ⁻¹)
    , is-monotone-Ord-is-prop _ _ _ )

------------------------------------------------------------------------
-- The "inl" branch: when the predicate is 0 at the top, fwd is `inl a`.
------------------------------------------------------------------------

thr-bot-lem : (n : ℕ) (a : Ord (suc n)) (b : 𝟚)
            → thr-pred n a b (inr ⋆) ≡ inl ⋆
            → thr-ord n a b ≡ inl a
thr-bot-lem n a b hyp =
    ap (λ s → monotone-ord-fwd-suc n s w₀) hyp
  ∙ ap inl (ap (monotone-ord-fwd n) w₀-eq ∙ monotone-ord-rinv n a)
  where
  w₀ : MonotoneOrd n
  w₀ = ( (λ o' → thr-pred n a b (inl o'))
       , (λ x y le → thr-mono n a b (inl x) (inl y) le) )
  w₀-eq : w₀ ≡ monotone-ord-bwd n a
  w₀-eq = to-Σ-≡ ( funext (λ o' → ap (pr₁ (monotone-ord-bwd n a)) (deface-inl o'))
                 , is-monotone-Ord-is-prop _ _ _ )

------------------------------------------------------------------------
-- The "non-bottom" indicator and its identification with the bwd value
-- at the top vertex (= sval at the top).  Rocq `thr_fn_ge` uses exactly
-- "a is above the threshold" — here it is `a ≠ ord-bot`.
------------------------------------------------------------------------

nbot : (n : ℕ) → Ord (suc n) → 𝟚
nbot zero    (inl ⋆) = inl ⋆
nbot zero    (inr ⋆) = inr ⋆
nbot (suc n) (inl x) = nbot n x
nbot (suc n) (inr ⋆) = inr ⋆

nbot-top : (n : ℕ) → nbot n (inr ⋆) ≡ inr ⋆
nbot-top zero    = refl _
nbot-top (suc n) = refl _

tag : {A : Type 𝓤₀} → 𝟙 + A → 𝟚
tag (inl ⋆) = inl ⋆
tag (inr _) = inr ⋆

baux-top : (n : ℕ) (r : 𝟙 + Ord (suc n))
         → pr₁ (monotone-ord-bwd-aux n r) (inr ⋆) ≡ tag r
baux-top n (inl ⋆)  = refl _
baux-top n (inr c') = refl _

tag-lift : (m : ℕ) (r : 𝟙 + Ord (suc m)) → tag (ord-unsuc-lift m r) ≡ tag r
tag-lift m (inl ⋆) = refl _
tag-lift m (inr c) = refl _

un-tag : (m : ℕ) (a : Ord (suc (suc m))) → tag (ord-unsuc m a) ≡ nbot (suc m) a
un-tag zero    (inl (inl ⋆)) = refl _
un-tag zero    (inl (inr ⋆)) = refl _
un-tag zero    (inr ⋆)       = refl _
un-tag (suc m) (inl (inl y)) = tag-lift m (ord-unsuc m (inl y)) ∙ un-tag m (inl y)
un-tag (suc m) (inl (inr ⋆)) = refl _
un-tag (suc m) (inr ⋆)       = refl _

sigtop : (n : ℕ) (a : Ord (suc n)) → sval n a (inr ⋆) ≡ nbot n a
sigtop zero    (inl ⋆) = refl _
sigtop zero    (inr ⋆) = refl _
sigtop (suc m) a       = baux-top m (ord-unsuc m a) ∙ un-tag m a

------------------------------------------------------------------------
-- The two clean closed-form facts (Rocq `thr_fn_ge` / `thr_fn_dnilast`).
------------------------------------------------------------------------

-- a above threshold (≠ bottom) ⇒ thr-ord n a b = ord-suc n a, any b.
thr-nonbot : (n : ℕ) (a : Ord (suc n)) (b : 𝟚)
           → nbot n a ≡ inr ⋆ → thr-ord n a b ≡ ord-suc n a
thr-nonbot n a b q =
  thr-top n a b (ap (λ s → interp b s (inr ⋆)) (sigtop n a ∙ q) ∙ interp-rr b)

-- b = 1 ⇒ thr-ord n a 1 = ord-suc n a, any a.
thr-ord-one : (n : ℕ) (a : Ord (suc n)) → thr-ord n a (inr ⋆) ≡ ord-suc n a
thr-ord-one n a = thr-top n a (inr ⋆) (refl _)

-- The b = 0 closed form, parametrised by the threshold value.
thr0val : (n : ℕ) → Ord (suc n) → 𝟚 → Ord (suc (suc n))
thr0val n a (inl ⋆) = inl a
thr0val n a (inr ⋆) = ord-suc n a

thr-zero-eq : (n : ℕ) (a : Ord (suc n)) (v : 𝟚)
            → sval n a (inr ⋆) ≡ v → thr-ord n a (inl ⋆) ≡ thr0val n a v
thr-zero-eq n a (inl ⋆) p = thr-bot-lem n a (inl ⋆) p
thr-zero-eq n a (inr ⋆) p = thr-top     n a (inl ⋆) p

thr0val-inl : (n : ℕ) (a : Ord (suc n)) (v : 𝟚)
            → inl (thr0val n a v) ≡ thr0val (suc n) (inl a) v
thr0val-inl n a (inl ⋆) = refl _
thr0val-inl n a (inr ⋆) = refl _

-- The dni-last commutation: inl ∘ thr-ord = thr-ord ∘ inl  (Rocq `thr_fn_dnilast`).
thr-dnilast : (n : ℕ) (a : Ord (suc n)) (b : 𝟚)
            → inl (thr-ord n a b) ≡ thr-ord (suc n) (inl a) b
thr-dnilast n a (inr ⋆) =
    ap inl (thr-ord-one n a) ∙ (thr-ord-one (suc n) (inl a)) ⁻¹
thr-dnilast n a (inl ⋆) =
    ap inl (thr-zero-eq n a (nbot n a) (sigtop n a))
  ∙ thr0val-inl n a (nbot n a)
  ∙ (thr-zero-eq (suc n) (inl a) (nbot n a) (sigtop (suc n) (inl a))) ⁻¹
