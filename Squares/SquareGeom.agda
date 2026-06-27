{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26, STREAM A — the concrete simplex square and its retract.
--
-- Builds the gluing square `Sq n` (Rocq `Sq`, Main.v 4689) out of the
-- already-existing geometry (`top`, `face`, `last-edge`, `eval-pt`), and
-- packages the two structural facts the induction needs:
--   * `base-Sq1`   : Sq 1 is a pushout            (Rocq `base_Sq1`, 5736)
--   * `retract-SSk`: Sq(k+2) is a square-retract of (Sq(k+1)) ×c 𝕀
--                                                  (Rocq `retract_SSk`, 5463)
--
-- The square's four corner maps are concrete; the three remaining facts
-- (`square-commutes`, `base-Sq1`, `retract-SSk`) are the genuine geometric
-- content.  `retract-SSk` is the lift of the postulate-free object-level
-- retract `sect`/`ret`/`ret-sect` (SimplexRetract) to the four square
-- corners, with the eight square-morphism commutations and four retract
-- laws being equations of maps into the posetal simplices (so each is a
-- `posetal-eq-objects` / terminal-uniqueness obligation).  They are stated
-- here against the committed `Square` interface so Stream B can build on
-- them; discharging them is the remaining Stream-A geometry task.
------------------------------------------------------------------------

module Squares.SquareGeom where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat using (𝕀; 𝕀-ob; 𝟚)
open import Category.Constructions using (dom; 𝕀₁; !)
open import Category.Pullbacks using (_×c_; π₁; π₂; ⟨_,_⟩; pair-β₁; pair-β₂; pair-η; equiv-inv-rinv)
open import Category.Product using (product-map; injl; injr; injl-product-map; injr-product-map; ipe)
open import Category.Exponentials using (Fun)
open import Interval.Interval using (Δ; Ord)
open import Simplices.FaceMap using (face)
open import Simplices.FaceTop using (top; c20-top)
open import Simplices.LastEdge using (last-edge)
open import Category.UnitIso using (eval-pt)
open import Squares.PushoutBase using (eval-pt-dom-last)
open import Simplices.FaceTopProof using (face-top)
open import Simplices.SimplexRetract using (sect; ret; ret-sect; pre-face-n; eval-at-top)
open import Simplices.SimplexRetractValues using
  (sect-π₁; sect-π₂; eval-at-top-top; pre-face-top; c20; c20-inj; 𝕀ob-inj;
   pre-face-val; eval-val; last-edge-c20; lastedge-ord; lastedge-sn2-pr1;
   lastedge-sn2-snd; vob; vob-ext; vob-pre; ret-c20)
open import Interval.OrdComb using (sn2-pr1; sn2-snd; sn2-pr1-inl; sn2-snd-face;
  thr-ord; thr-dnilast; thr-nonbot; ord-suc-top; nbot-top)
open import Interval.FaceOrdCompat using (c20-face-gen-u)
open import Posetal.Posetal using (posetal-eq-objects; Delta-posetal; I-posetal)
open import Squares.Square

------------------------------------------------------------------------
-- The concrete corner maps (Rocq v0_Δ1 / vn / lastedge / spine_incl)
------------------------------------------------------------------------

-- vertex 0 of Δ¹ : the domain of the unique non-degenerate edge of Δ¹.
v0-Δ1 : Map 𝟏c (Δ (suc zero))
v0-Δ1 = dom (last-edge zero)

-- the last edge as a 1-simplex Δ¹ → Δ(suc n), via the iso eval-pt : Δ¹ ≅ 𝕀.
lastedge : (n : ℕ) → Map (Δ (suc zero)) (Δ (suc n))
lastedge n = comp (last-edge n) eval-pt

-- Rocq `square_commutes` (Main.v ~4689): the gluing square commutes.
-- LHS collapses to dom (last-edge n): the eval-pt iso sends vertex 0 of Δ¹ to
-- 𝕀₀ (`eval-pt-dom-last`), so lastedge ∘ v0 = (last-edge n) ∘ 𝕀₀ = dom(last-edge n);
-- RHS is `face-top`.  Both are the n-th vertex of Δ(suc n).
square-commutes : (n : ℕ)
  → comp (lastedge n) v0-Δ1 ≡ comp (face n) (top n)
square-commutes n =
    composeA (last-edge n) eval-pt (dom (last-edge zero))
  ∙ ap (comp (last-edge n)) eval-pt-dom-last
  ∙ (face-top n) ⁻¹

------------------------------------------------------------------------
-- The square Sq n  (Rocq `Sq`, Main.v 4689)
------------------------------------------------------------------------

Sq : ℕ → Square
Sq n = mk-square 𝟏c (Δ (suc zero)) (Δ n) (Δ (suc n))
         v0-Δ1 (top n) (lastedge n) (face n)
         (square-commutes n)

------------------------------------------------------------------------
-- The two structural theorems (Stream-A geometry — stated for Stream B)
------------------------------------------------------------------------

-- NB `base-Sq1 : is-pushout-square (Sq 1)` is DERIVED from the Segal axiom
-- in `SegalGeom` (the geometric coface reformulation), not postulated here.

------------------------------------------------------------------------
-- The square retract `retract-SSk` (Rocq `retract_SSk`, Main.v 5463).
--
-- `Sq (suc (suc k))` is a square-retract of `times-I (Sq (suc k))`.  Index
-- shift: with `n := suc k`, the corners line up with the geometric retract
-- `sect`/`ret`/`ret-sect` (Δ(n+2) ◁ Δ(n+1) ×c 𝕀, SimplexRetract).
--   Sq(suc(suc k)):       A=𝟏c       B=Δ1        C=Δ(2+k)        D=Δ(3+k)
--   times-I (Sq(suc k)):  A=𝟏c×c𝕀    B=Δ1×c𝕀     C=Δ(1+k)×c𝕀     D=Δ(2+k)×c𝕀
------------------------------------------------------------------------

-- the "glue at 𝕀₁" section  X → X ×c 𝕀  (Rocq `glue_right constant_1`)
glue-1 : (X : Cat) → Map X (X ×c 𝕀)
glue-1 X = ⟨ idMap X , comp 𝕀₁ (! X) ⟩

-- projection laws of glue-1 (injl = π₁, injr = π₂)
glue-injl : (X : Cat) → comp injl (glue-1 X) ≡ idMap X
glue-injl X = pair-β₁ (idMap X) (comp 𝕀₁ (! X))

glue-injr : (X : Cat) → comp injr (glue-1 X) ≡ comp 𝕀₁ (! X)
glue-injr X = pair-β₂ (idMap X) (comp 𝕀₁ (! X))

------------------------------------------------------------------------
-- The two easy commutations (`smt-*`): maps with terminal data, pure
-- product/terminal algebra (no ordinal layer).
------------------------------------------------------------------------

-- smt-s : comp (sqt Q) smA ≡ comp smB (sqt P), with smA = glue-1 𝟏c,
-- smB = glue-1 (Δ 1), sqt = v0-Δ1.
smt-s : (k : ℕ)
  → comp (product-map v0-Δ1 (idMap 𝕀)) (glue-1 𝟏c)
  ≡ comp (glue-1 (Δ (suc zero))) v0-Δ1
smt-s k = ipe _ _ el er
  where
  el : comp injl (comp (product-map v0-Δ1 (idMap 𝕀)) (glue-1 𝟏c))
     ≡ comp injl (comp (glue-1 (Δ (suc zero))) v0-Δ1)
  el = comp-assoc injl (product-map v0-Δ1 (idMap 𝕀)) (glue-1 𝟏c)
     ∙ ap (λ h → comp h (glue-1 𝟏c)) (injl-product-map v0-Δ1 (idMap 𝕀))
     ∙ composeA v0-Δ1 injl (glue-1 𝟏c)
     ∙ ap (comp v0-Δ1) (glue-injl 𝟏c)
     ∙ comp-id-r v0-Δ1
     ∙ (comp-id-l v0-Δ1) ⁻¹
     ∙ ap (λ h → comp h v0-Δ1) ((glue-injl (Δ (suc zero))) ⁻¹)
     ∙ (comp-assoc injl (glue-1 (Δ (suc zero))) v0-Δ1) ⁻¹
  er : comp injr (comp (product-map v0-Δ1 (idMap 𝕀)) (glue-1 𝟏c))
     ≡ comp injr (comp (glue-1 (Δ (suc zero))) v0-Δ1)
  er = comp-assoc injr (product-map v0-Δ1 (idMap 𝕀)) (glue-1 𝟏c)
     ∙ ap (λ h → comp h (glue-1 𝟏c)) (injr-product-map v0-Δ1 (idMap 𝕀))
     ∙ composeA (idMap 𝕀) injr (glue-1 𝟏c)
     ∙ ap (comp (idMap 𝕀)) (glue-injr 𝟏c)
     ∙ comp-id-l (comp 𝕀₁ (! 𝟏c))
     ∙ ap (comp 𝕀₁) (singletons-are-props (terminal 𝟏c) (! 𝟏c) (comp (! (Δ (suc zero))) v0-Δ1))
     ∙ (composeA 𝕀₁ (! (Δ (suc zero))) v0-Δ1) ⁻¹
     ∙ ap (λ h → comp h v0-Δ1) ((glue-injr (Δ (suc zero))) ⁻¹)
     ∙ (comp-assoc injr (glue-1 (Δ (suc zero))) v0-Δ1) ⁻¹

-- smt-r : comp (sqt P) smA ≡ comp smB (sqt Q), with smA = ! (𝟏c ×c 𝕀),
-- smB = π₁ (Δ 1) 𝕀 = injl, sqt P = v0-Δ1, sqt Q = product-map v0-Δ1 id.
smt-r : (k : ℕ)
  → comp v0-Δ1 (! (𝟏c ×c 𝕀))
  ≡ comp (π₁ (Δ (suc zero)) 𝕀) (product-map v0-Δ1 (idMap 𝕀))
smt-r k =
    ap (comp v0-Δ1) (singletons-are-props (terminal (𝟏c ×c 𝕀))
                       (! (𝟏c ×c 𝕀)) (π₁ 𝟏c 𝕀))
  ∙ (injl-product-map v0-Δ1 (idMap 𝕀)) ⁻¹

-- sml-s : comp (sql Q) smA ≡ comp smC (sql P).  Both sides are maps 𝟏c →
-- Δ(suc k) ×c 𝕀; `ipe` reduces to the two projections, then the section
-- value lemmas (pre-face-n@top = top, eval-at-top@top = 𝕀₁).
sml-s : (k : ℕ)
  → comp (product-map (top (suc k)) (idMap 𝕀)) (glue-1 𝟏c)
  ≡ comp (sect k) (top (suc (suc k)))
sml-s k = ipe _ _ el er
  where
  el : comp injl (comp (product-map (top (suc k)) (idMap 𝕀)) (glue-1 𝟏c))
     ≡ comp injl (comp (sect k) (top (suc (suc k))))
  el = comp-assoc injl (product-map (top (suc k)) (idMap 𝕀)) (glue-1 𝟏c)
     ∙ ap (λ h → comp h (glue-1 𝟏c)) (injl-product-map (top (suc k)) (idMap 𝕀))
     ∙ composeA (top (suc k)) injl (glue-1 𝟏c)
     ∙ ap (comp (top (suc k))) (glue-injl 𝟏c)
     ∙ comp-id-r (top (suc k))
     ∙ (pre-face-top k) ⁻¹
     ∙ ap (λ h → comp h (top (suc (suc k)))) ((sect-π₁ k) ⁻¹)
     ∙ (comp-assoc injl (sect k) (top (suc (suc k)))) ⁻¹
  er : comp injr (comp (product-map (top (suc k)) (idMap 𝕀)) (glue-1 𝟏c))
     ≡ comp injr (comp (sect k) (top (suc (suc k))))
  er = comp-assoc injr (product-map (top (suc k)) (idMap 𝕀)) (glue-1 𝟏c)
     ∙ ap (λ h → comp h (glue-1 𝟏c)) (injr-product-map (top (suc k)) (idMap 𝕀))
     ∙ composeA (idMap 𝕀) injr (glue-1 𝟏c)
     ∙ ap (comp (idMap 𝕀)) (glue-injr 𝟏c)
     ∙ comp-id-l (comp 𝕀₁ (! 𝟏c))
     ∙ ap (comp 𝕀₁) (singletons-are-props (terminal 𝟏c) (! 𝟏c) (idMap 𝟏c))
     ∙ comp-id-r 𝕀₁
     ∙ (eval-at-top-top k) ⁻¹
     ∙ ap (λ h → comp h (top (suc (suc k)))) ((sect-π₂ k) ⁻¹)
     ∙ (comp-assoc injr (sect k) (top (suc (suc k)))) ⁻¹

-- The 5 remaining commutations.  Each reduces — via `ipe` to its two
-- projections, then `posetal-eq-objects (Delta-posetal _)` / `I-posetal`
-- and the vertex bridges in `SimplexRetractValues`
-- (`pre-face-val`/`eval-val` = c20∘pre-face = `sn2-pr1`, 𝕀-ob∘eval-at-top =
-- `sn2-snd`) plus `c20-face-gen-u` — to PURE ordinal identities in
-- `OrdComb`:
--   * smb-s : needs  inl (sn2-pr1 n c) ≡ sn2-pr1 (suc n) (inl c)
--             [Rocq `Sn2inv_dnilast_pr1`; the inl/π₁ leg, the `el` side]
--          +  sn2-snd n c ≡ sn2-snd (suc n) (inl c)
--             [= `OrdComb.sn2-snd-face`, ALREADY PROVED; the `er` side].
--   * smr-s : the source is Δ 1, so the two objects split via `two-values`;
--             needs the `lastedge` vertex values (`lastedge-ord`,
--             Rocq `lastedge_fn_0/1`) and `sn2-pr1`/`sn2-snd` at the
--             `dni_first`/`dni_last` images (Rocq `Sn2inv_dnifirst_*`).
--   * sml-r / smr-r / smb-r : the `ret`-side; need the object value of
--             `ret` (Rocq `retr_thr_val`, the `ret-p`/`thr_fn` formula —
--             `ret-p-expand` in SimplexRetract is the raw material).
-- `OrdComb.sn2-snd-face`, the general bridges, and `sml-s` (fully proved)
-- are the discharged pieces of this programme.
-- smr-s : comp (sqr Q) smB ≡ comp smD (sqr P).  Source Δ1; `ipe` splits into
-- the injl-leg (Δ1→Δ(2+k), via the `last-edge` vertex bridge + `lastedge-sn2-pr1`)
-- and the injr-leg (Δ1→𝕀, constant 𝕀₁, via `lastedge-sn2-snd`).  Recall
-- `lastedge n = comp (last-edge n) eval-pt`.
smr-s : (k : ℕ)
  → comp (product-map (lastedge (suc k)) (idMap 𝕀)) (glue-1 (Δ (suc zero)))
  ≡ comp (sect (suc k)) (lastedge (suc (suc k)))
smr-s k = ipe _ _ el er
  where
  key-el : lastedge (suc k) ≡ comp (pre-face-n (suc k)) (lastedge (suc (suc k)))
  key-el = posetal-eq-objects (Delta-posetal (suc (suc k))) (λ x →
    c20-inj (suc (suc k))
      ( ap (c20 (suc (suc k))) (composeA (last-edge (suc k)) eval-pt x)
      ∙ last-edge-c20 (suc k) (comp eval-pt x)
      ∙ lastedge-sn2-pr1 k (pr₁ 𝕀-ob (comp eval-pt x))
      ∙ ap (sn2-pr1 (suc k)) ((last-edge-c20 (suc (suc k)) (comp eval-pt x)) ⁻¹)
      ∙ (pre-face-val (suc k) (comp (last-edge (suc (suc k))) (comp eval-pt x))) ⁻¹
      ∙ ap (c20 (suc (suc k)))
          ( ap (comp (pre-face-n (suc k))) ((composeA (last-edge (suc (suc k))) eval-pt x) ⁻¹)
          ∙ comp-assoc (pre-face-n (suc k)) (lastedge (suc (suc k))) x ) ))

  key-er : comp 𝕀₁ (! (Δ (suc zero)))
         ≡ comp (eval-at-top (suc k)) (lastedge (suc (suc k)))
  key-er = posetal-eq-objects I-posetal (λ x →
    𝕀ob-inj
      ( ap (pr₁ 𝕀-ob)
          ( composeA 𝕀₁ (! (Δ (suc zero))) x
          ∙ ap (comp 𝕀₁) (singletons-are-props (terminal 𝟏c)
                            (comp (! (Δ (suc zero))) x) (idMap 𝟏c))
          ∙ comp-id-r 𝕀₁ )
      ∙ equiv-inv-rinv 𝕀-ob (inr ⋆)
      ∙ lastedge-sn2-snd k (pr₁ 𝕀-ob (comp eval-pt x))
      ∙ ( ap (pr₁ 𝕀-ob) (composeA (eval-at-top (suc k)) (lastedge (suc (suc k))) x)
        ∙ eval-val (suc k) (comp (lastedge (suc (suc k))) x)
        ∙ ap (sn2-snd (suc k))
            ( ap (c20 (suc (suc (suc k)))) (composeA (last-edge (suc (suc k))) eval-pt x)
            ∙ last-edge-c20 (suc (suc k)) (comp eval-pt x) ) ) ⁻¹ ))

  el : comp injl (comp (product-map (lastedge (suc k)) (idMap 𝕀)) (glue-1 (Δ (suc zero))))
     ≡ comp injl (comp (sect (suc k)) (lastedge (suc (suc k))))
  el = comp-assoc injl (product-map (lastedge (suc k)) (idMap 𝕀)) (glue-1 (Δ (suc zero)))
     ∙ ap (λ h → comp h (glue-1 (Δ (suc zero)))) (injl-product-map (lastedge (suc k)) (idMap 𝕀))
     ∙ composeA (lastedge (suc k)) injl (glue-1 (Δ (suc zero)))
     ∙ ap (comp (lastedge (suc k))) (glue-injl (Δ (suc zero)))
     ∙ comp-id-r (lastedge (suc k))
     ∙ key-el
     ∙ ap (λ h → comp h (lastedge (suc (suc k)))) ((sect-π₁ (suc k)) ⁻¹)
     ∙ (comp-assoc injl (sect (suc k)) (lastedge (suc (suc k)))) ⁻¹

  er : comp injr (comp (product-map (lastedge (suc k)) (idMap 𝕀)) (glue-1 (Δ (suc zero))))
     ≡ comp injr (comp (sect (suc k)) (lastedge (suc (suc k))))
  er = comp-assoc injr (product-map (lastedge (suc k)) (idMap 𝕀)) (glue-1 (Δ (suc zero)))
     ∙ ap (λ h → comp h (glue-1 (Δ (suc zero)))) (injr-product-map (lastedge (suc k)) (idMap 𝕀))
     ∙ composeA (idMap 𝕀) injr (glue-1 (Δ (suc zero)))
     ∙ comp-id-l (comp injr (glue-1 (Δ (suc zero))))
     ∙ glue-injr (Δ (suc zero))
     ∙ key-er
     ∙ ap (λ h → comp h (lastedge (suc (suc k)))) ((sect-π₂ (suc k)) ⁻¹)
     ∙ (comp-assoc injr (sect (suc k)) (lastedge (suc (suc k)))) ⁻¹

-- smb-s : comp (sqb Q) smC ≡ comp smD (sqb P).  Source Δ(2+k); `ipe` splits
-- into the injl-leg (a Δ(2+k)→Δ(2+k) simplicial identity, discharged by
-- `posetal-eq-objects (Delta-posetal _)` + `c20-inj` + `pre-face-val` +
-- `c20-face-gen-u` + the ordinal `sn2-pr1-inl`) and the injr-leg (a Δ(2+k)→𝕀
-- equation, via `I-posetal` + `𝕀ob-inj` + `eval-val` + `sn2-snd-face`).
smb-s : (k : ℕ)
  → comp (product-map (face (suc k)) (idMap 𝕀)) (sect k)
  ≡ comp (sect (suc k)) (face (suc (suc k)))
smb-s k = ipe _ _ el er
  where
  key-el : comp (face (suc k)) (pre-face-n k)
         ≡ comp (pre-face-n (suc k)) (face (suc (suc k)))
  key-el = posetal-eq-objects (Delta-posetal (suc (suc k))) (λ z →
    c20-inj (suc (suc k))
      ( ap (c20 (suc (suc k))) (composeA (face (suc k)) (pre-face-n k) z)
      ∙ c20-face-gen-u (suc k) (comp (pre-face-n k) z)
      ∙ ap inl (pre-face-val k z)
      ∙ sn2-pr1-inl k (c20 (suc (suc k)) z)
      ∙ ap (sn2-pr1 (suc k)) (c20-face-gen-u (suc (suc k)) z) ⁻¹
      ∙ (pre-face-val (suc k) (comp (face (suc (suc k))) z)) ⁻¹
      ∙ ap (c20 (suc (suc k))) (composeA (pre-face-n (suc k)) (face (suc (suc k))) z) ⁻¹ ))

  key-er : eval-at-top k ≡ comp (eval-at-top (suc k)) (face (suc (suc k)))
  key-er = posetal-eq-objects I-posetal (λ z →
    𝕀ob-inj
      ( eval-val k z
      ∙ sn2-snd-face k (c20 (suc (suc k)) z)
      ∙ ap (sn2-snd (suc k)) (c20-face-gen-u (suc (suc k)) z) ⁻¹
      ∙ (eval-val (suc k) (comp (face (suc (suc k))) z)) ⁻¹
      ∙ ap (pr₁ 𝕀-ob) (composeA (eval-at-top (suc k)) (face (suc (suc k))) z) ⁻¹ ))

  el : comp injl (comp (product-map (face (suc k)) (idMap 𝕀)) (sect k))
     ≡ comp injl (comp (sect (suc k)) (face (suc (suc k))))
  el = comp-assoc injl (product-map (face (suc k)) (idMap 𝕀)) (sect k)
     ∙ ap (λ h → comp h (sect k)) (injl-product-map (face (suc k)) (idMap 𝕀))
     ∙ composeA (face (suc k)) injl (sect k)
     ∙ ap (comp (face (suc k))) (sect-π₁ k)
     ∙ key-el
     ∙ ap (λ h → comp h (face (suc (suc k)))) ((sect-π₁ (suc k)) ⁻¹)
     ∙ (comp-assoc injl (sect (suc k)) (face (suc (suc k)))) ⁻¹

  er : comp injr (comp (product-map (face (suc k)) (idMap 𝕀)) (sect k))
     ≡ comp injr (comp (sect (suc k)) (face (suc (suc k))))
  er = comp-assoc injr (product-map (face (suc k)) (idMap 𝕀)) (sect k)
     ∙ ap (λ h → comp h (sect k)) (injr-product-map (face (suc k)) (idMap 𝕀))
     ∙ composeA (idMap 𝕀) injr (sect k)
     ∙ comp-id-l (comp injr (sect k))
     ∙ sect-π₂ k
     ∙ key-er
     ∙ ap (λ h → comp h (face (suc (suc k)))) ((sect-π₂ (suc k)) ⁻¹)
     ∙ (comp-assoc injr (sect (suc k)) (face (suc (suc k)))) ⁻¹

------------------------------------------------------------------------
-- The `sr-r` (retraction) commutations.  Each needs the object value of
-- `ret` (Rocq `retr_thr_val`; raw material `ret-p-expand` in
-- SimplexRetract) — the ordinal `ret-p`/`thr_fn` formula — and would be
-- discharged by the same `ipe → posetal-eq-objects → c20-inj` wrapper.
------------------------------------------------------------------------

-- All three are equations of maps INTO a posetal simplex, so `vob-ext`
-- reduces each to a vertex equation, then `ret-c20` rewrites the `ret`
-- side to `thr-ord` and the OrdComb identities finish it.

-- sml-r : the top-corner ret leg.  Both vertices are the top ordinal.
sml-r : (k : ℕ)
  → comp (top (suc (suc k))) (! (𝟏c ×c 𝕀))
  ≡ comp (ret k) (product-map (top (suc k)) (idMap 𝕀))
sml-r k = vob-ext (suc (suc k)) (λ x → lhs x ∙ (rhs x) ⁻¹)
  where
  N = suc (suc k)
  PM : Map (𝟏c ×c 𝕀) (Δ (suc k) ×c 𝕀)
  PM = product-map (top (suc k)) (idMap 𝕀)
  lhs : (x : Ob (𝟏c ×c 𝕀))
      → vob N (comp (top (suc (suc k))) (! (𝟏c ×c 𝕀))) x ≡ inr ⋆
  lhs x =
      vob-pre N (top (suc (suc k))) (! (𝟏c ×c 𝕀)) x
    ∙ ap (λ z → c20 N (comp (top (suc (suc k))) z))
         (singletons-are-props (terminal 𝟏c) (comp (! (𝟏c ×c 𝕀)) x) (idMap 𝟏c))
    ∙ ap (c20 N) (comp-id-r (top (suc (suc k))))
    ∙ c20-top (suc (suc k))
  rhs : (x : Ob (𝟏c ×c 𝕀)) → vob N (comp (ret k) PM) x ≡ inr ⋆
  rhs x =
      vob-pre N (ret k) PM x
    ∙ ret-c20 k (comp PM x)
    ∙ ap (λ z → thr-ord k z (pr₁ 𝕀-ob (comp (π₂ (Δ (suc k)) 𝕀) (comp PM x)))) a-val
    ∙ thr-nonbot k (inr ⋆) (pr₁ 𝕀-ob (comp (π₂ (Δ (suc k)) 𝕀) (comp PM x))) (nbot-top k)
    ∙ ord-suc-top k
    where
    a-val : c20 (suc k) (comp (π₁ (Δ (suc k)) 𝕀) (comp PM x)) ≡ inr ⋆
    a-val =
        ap (c20 (suc k))
           ( (composeA (π₁ (Δ (suc k)) 𝕀) PM x) ⁻¹
           ∙ ap (λ h → comp h x) (injl-product-map (top (suc k)) (idMap 𝕀))
           ∙ composeA (top (suc k)) injl x
           ∙ ap (comp (top (suc k)))
               (singletons-are-props (terminal 𝟏c) (comp injl x) (idMap 𝟏c)) )
      ∙ ap (c20 (suc k)) (comp-id-r (top (suc k)))
      ∙ c20-top (suc k)

-- smr-r : the right-corner ret leg.  Source Δ1; case on the 𝕀-coord `c`.
smr-r : (k : ℕ)
  → comp (lastedge (suc (suc k))) (π₁ (Δ (suc zero)) 𝕀)
  ≡ comp (ret (suc k)) (product-map (lastedge (suc k)) (idMap 𝕀))
smr-r k = vob-ext (suc (suc (suc k))) (λ x → lhs x ∙ smr-key k (cc x) (bb x) ∙ (rhs x) ⁻¹)
  where
  N = suc (suc (suc k))
  PM : Map (Δ (suc zero) ×c 𝕀) (Δ (suc (suc k)) ×c 𝕀)
  PM = product-map (lastedge (suc k)) (idMap 𝕀)
  p1 : Ob (Δ (suc zero) ×c 𝕀) → Ob (Δ (suc zero))
  p1 x = comp (π₁ (Δ (suc zero)) 𝕀) x
  cc : Ob (Δ (suc zero) ×c 𝕀) → 𝟚
  cc x = pr₁ 𝕀-ob (comp eval-pt (p1 x))
  bb : Ob (Δ (suc zero) ×c 𝕀) → 𝟚
  bb x = pr₁ 𝕀-ob (comp (π₂ (Δ (suc (suc k))) 𝕀) (comp PM x))

  smr-key : (k : ℕ) (c b : 𝟚)
    → lastedge-ord (suc (suc k)) c ≡ thr-ord (suc k) (lastedge-ord (suc k) c) b
  smr-key k (inl ⋆) b = (thr-nonbot (suc k) (inl (inr ⋆)) b (nbot-top k) ∙ ap inl (ord-suc-top k)) ⁻¹
  smr-key k (inr ⋆) b = (thr-nonbot (suc k) (inr ⋆)       b (refl _) ∙ ord-suc-top (suc k)) ⁻¹

  lhs : (x : Ob (Δ (suc zero) ×c 𝕀))
      → vob N (comp (lastedge (suc (suc k))) (π₁ (Δ (suc zero)) 𝕀)) x ≡ lastedge-ord (suc (suc k)) (cc x)
  lhs x =
      vob-pre N (lastedge (suc (suc k))) (π₁ (Δ (suc zero)) 𝕀) x
    ∙ ap (c20 N) (composeA (last-edge (suc (suc k))) eval-pt (p1 x))
    ∙ last-edge-c20 (suc (suc k)) (comp eval-pt (p1 x))

  rhs : (x : Ob (Δ (suc zero) ×c 𝕀))
      → vob N (comp (ret (suc k)) PM) x ≡ thr-ord (suc k) (lastedge-ord (suc k) (cc x)) (bb x)
  rhs x =
      vob-pre N (ret (suc k)) PM x
    ∙ ret-c20 (suc k) (comp PM x)
    ∙ ap (λ z → thr-ord (suc k) z (bb x)) a-val
    where
    a-val : c20 (suc (suc k)) (comp (π₁ (Δ (suc (suc k))) 𝕀) (comp PM x))
          ≡ lastedge-ord (suc k) (cc x)
    a-val =
        ap (c20 (suc (suc k)))
           ( (composeA (π₁ (Δ (suc (suc k))) 𝕀) PM x) ⁻¹
           ∙ ap (λ h → comp h x) (injl-product-map (lastedge (suc k)) (idMap 𝕀))
           ∙ composeA (lastedge (suc k)) injl x
           ∙ composeA (last-edge (suc k)) eval-pt (p1 x) )
      ∙ last-edge-c20 (suc k) (comp eval-pt (p1 x))

-- smb-r : the bottom-corner ret leg.  Uses the dni-last identity.
smb-r : (k : ℕ)
  → comp (face (suc (suc k))) (ret k)
  ≡ comp (ret (suc k)) (product-map (face (suc k)) (idMap 𝕀))
smb-r k = vob-ext (suc (suc (suc k))) (λ x → lhs x ∙ thr-dnilast k (aa x) (bb x) ∙ (rhs x) ⁻¹)
  where
  N = suc (suc (suc k))
  PM : Map (Δ (suc k) ×c 𝕀) (Δ (suc (suc k)) ×c 𝕀)
  PM = product-map (face (suc k)) (idMap 𝕀)
  aa : Ob (Δ (suc k) ×c 𝕀) → Ord (suc k)
  aa x = c20 (suc k) (comp (π₁ (Δ (suc k)) 𝕀) x)
  bb : Ob (Δ (suc k) ×c 𝕀) → 𝟚
  bb x = pr₁ 𝕀-ob (comp (π₂ (Δ (suc k)) 𝕀) x)

  lhs : (x : Ob (Δ (suc k) ×c 𝕀))
      → vob N (comp (face (suc (suc k))) (ret k)) x ≡ inl (thr-ord k (aa x) (bb x))
  lhs x =
      vob-pre N (face (suc (suc k))) (ret k) x
    ∙ c20-face-gen-u (suc (suc k)) (comp (ret k) x)
    ∙ ap inl (ret-c20 k x)

  rhs : (x : Ob (Δ (suc k) ×c 𝕀))
      → vob N (comp (ret (suc k)) PM) x ≡ thr-ord (suc k) (inl (aa x)) (bb x)
  rhs x =
      vob-pre N (ret (suc k)) PM x
    ∙ ret-c20 (suc k) (comp PM x)
    ∙ ap (λ z → thr-ord (suc k) z (pr₁ 𝕀-ob (comp (π₂ (Δ (suc (suc k))) 𝕀) (comp PM x)))) a-val
    ∙ ap (λ z → thr-ord (suc k) (inl (aa x)) z) b-val
    where
    a-val : c20 (suc (suc k)) (comp (π₁ (Δ (suc (suc k))) 𝕀) (comp PM x)) ≡ inl (aa x)
    a-val =
        ap (c20 (suc (suc k)))
           ( (composeA (π₁ (Δ (suc (suc k))) 𝕀) PM x) ⁻¹
           ∙ ap (λ h → comp h x) (injl-product-map (face (suc k)) (idMap 𝕀))
           ∙ composeA (face (suc k)) injl x )
      ∙ c20-face-gen-u (suc k) (comp injl x)
    b-val : pr₁ 𝕀-ob (comp (π₂ (Δ (suc (suc k))) 𝕀) (comp PM x)) ≡ bb x
    b-val =
      ap (pr₁ 𝕀-ob)
         ( (composeA (π₂ (Δ (suc (suc k))) 𝕀) PM x) ⁻¹
         ∙ ap (λ h → comp h x) (injr-product-map (face (suc k)) (idMap 𝕀))
         ∙ composeA (idMap 𝕀) injr x
         ∙ comp-id-l (comp injr x) )

------------------------------------------------------------------------
-- The two square morphisms and the four retract laws
------------------------------------------------------------------------

-- corner retract law A: terminal uniqueness
law-A : (k : ℕ) → comp (! (𝟏c ×c 𝕀)) (glue-1 𝟏c) ≡ idMap 𝟏c
law-A k = singletons-are-props (terminal 𝟏c) _ _

-- corner retract law B: pair-β₁
law-B : (k : ℕ) → comp (π₁ (Δ (suc zero)) 𝕀) (glue-1 (Δ (suc zero))) ≡ idMap (Δ (suc zero))
law-B k = pair-β₁ (idMap (Δ (suc zero))) (comp 𝕀₁ (! (Δ (suc zero))))

sr-s-mor : (k : ℕ) → square-morphism (Sq (suc (suc k))) (times-I (Sq (suc k)))
sr-s-mor k = mk-square-morphism
  (glue-1 𝟏c) (glue-1 (Δ (suc zero))) (sect k) (sect (suc k))
  (smt-s k) (sml-s k) (smr-s k) (smb-s k)

sr-r-mor : (k : ℕ) → square-morphism (times-I (Sq (suc k))) (Sq (suc (suc k)))
sr-r-mor k = mk-square-morphism
  (! (𝟏c ×c 𝕀)) (π₁ (Δ (suc zero)) 𝕀) (ret k) (ret (suc k))
  (smt-r k) (sml-r k) (smr-r k) (smb-r k)

retract-SSk : (k : ℕ)
  → square-retract (Sq (suc (suc k))) (times-I (Sq (suc k)))
retract-SSk k = mk-square-retract
  (sr-s-mor k) (sr-r-mor k)
  (law-A k) (law-B k) (ret-sect k) (ret-sect (suc k))
