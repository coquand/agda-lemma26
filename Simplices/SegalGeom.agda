{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26, GEOMETRIC LAYER — the Segal axiom in geometric form, and base-Sq1.
--
-- axioms.pdf Axiom 21 states the Segal axiom AS a pushout square: Δ² is the
-- pushout of  I ← 1 → I  glued at a vertex, with the CONCRETE coface maps
-- 01 / 12.  Rocq matches this (`d01 := degeneracy_map Δ2_vertice_2`, etc.).
-- The Agda `Segal` module instead postulates `d₀₁`/`d₁₂` abstractly (only
-- endpoint axioms), which severs the link to the geometric edges.
--
-- This module restores that link: it pins the abstract cofaces to the
-- geometric edges `face 1` / `lastedge 1` (transported along the iso
-- eval-pt : 𝕀 ≅ Δ¹), and then DERIVES `base-Sq1 : is-pushout-square (Sq 1)`
-- from the existing Segal axiom by the cone ↔ composable-pair reshuffle —
-- exactly as Rocq's `base_Sq1` (Main.v 5736) reshuffles `segal_UP_axiom`.
------------------------------------------------------------------------

module Simplices.SegalGeom where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat using (𝕀; 𝟚; Mor; equiv-inj)
open import Category.Constructions using (𝕀₀; 𝕀₁; dom; cod; Hom; equiv-inv; cod-nat; dom-nat)
open import Category.Pullbacks using (equiv-inv-rinv; equiv-inv-linv)
open import Category.Exponentials using (Fun)
open import Interval.Interval using (Δ; invertible-to-equiv; equiv-comp)
open import Simplices.Segal using (ComposablePair; segal-comparison; segal-equiv;
  segal-is-equiv; d₀₁; d₁₂; segal-comm)
open import Simplices.FaceMap using (face)
open import Simplices.FaceTop using (top)
open import Simplices.LastEdge using (last-edge)
open import Category.UnitIso using (eval-pt; eval-pt-isIso)
open import Squares.PushoutBase using (eval-pt-top1; eval-pt-dom-last)
open import Squares.PushoutProof using (eval-pt-inv; eval-pt-rinv; eval-pt-linv)
open import Foundations.SigmaEquiv using (Σ-change-of-base; Σ-fiberwise-equiv;
  post-comp-path-equiv; pre-comp-path-equiv)
open import Squares.SquareGeom using (Sq; v0-Δ1; lastedge; square-commutes)
open import Squares.Square
open import Foundations.Coherence using (ap-∙; ap-⁻¹; ∙-cong; cancel-left)
open import Foundations.HLevels using (ob-Δ-is-set)
open import Solvers.GroupoidSolver using (Expr; ι; ε; _⊕_; inv; eval; solveG; cancL; cancR)

------------------------------------------------------------------------
-- Generic equivalence infrastructure
------------------------------------------------------------------------

ap2 : {A B C : Type 𝓤} (f : A → B → C) {a a' : A} {b b' : B}
    → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f (refl _) (refl _) = refl _

≃-sym : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → B ≃ A
≃-sym e = equiv-inv e ,
  invertible-to-equiv (equiv-inv e)
    (pr₁ e , equiv-inv-linv e , equiv-inv-rinv e)

homotopic-is-equiv : {A : Type 𝓤} {B : Type 𝓥} {f g : A → B}
  → ((x : A) → f x ≡ g x) → is-equiv f → is-equiv g
homotopic-is-equiv {f = f} {g} htpy ef = transport is-equiv (funext htpy) ef

×-equiv : {A A' B B' : Type 𝓤} → A ≃ A' → B ≃ B' → (A × B) ≃ (A' × B')
×-equiv eA eB =
  (λ p → pr₁ eA (pr₁ p) , pr₁ eB (pr₂ p)) ,
  invertible-to-equiv _
    ((λ p → equiv-inv eA (pr₁ p) , equiv-inv eB (pr₂ p)) ,
     (λ p → ap2 _,_ (equiv-inv-rinv eA (pr₁ p)) (equiv-inv-rinv eB (pr₂ p))) ,
     (λ p → ap2 _,_ (equiv-inv-linv eA (pr₁ p)) (equiv-inv-linv eB (pr₂ p))))

------------------------------------------------------------------------
-- The reformulated Segal axiom: the abstract cofaces ARE the geometric
-- edges (axioms.pdf Axiom 21 / Rocq `degeneracy_map`).  This is the only
-- new postulate; everything below is derived.
------------------------------------------------------------------------

postulate
  segal-coface-01 : d₀₁ ≡ comp (face (suc zero)) eval-pt-inv
  segal-coface-12 : d₁₂ ≡ comp (lastedge (suc zero)) eval-pt-inv

------------------------------------------------------------------------
-- The iso eval-pt : 𝕀 ≅ Δ¹ sends 𝕀₀/𝕀₁ to the two vertices of Δ¹
------------------------------------------------------------------------

-- These iso facts are heavy (equiv-inj on eval-pt-isIso); kept `opaque`
-- so the reshuffle proof treats them as symbolic atoms (else ~37 s blowup).
opaque
  -- comp eval-pt-inv 𝕀₁ ≡ top 1  (top vertex)
  ei1 : comp eval-pt-inv 𝕀₁ ≡ top (suc zero)
  ei1 = equiv-inj (post-comp eval-pt 𝟏c) (eval-pt-isIso 𝟏c)
    ( comp-assoc eval-pt eval-pt-inv 𝕀₁
    ∙ ap (λ m → comp m 𝕀₁) eval-pt-rinv
    ∙ comp-id-l 𝕀₁
    ∙ eval-pt-top1 ⁻¹ )

  -- comp eval-pt-inv 𝕀₀ ≡ v0-Δ1  (bottom vertex = dom (last-edge 0))
  ei0 : comp eval-pt-inv 𝕀₀ ≡ v0-Δ1
  ei0 = equiv-inj (post-comp eval-pt 𝟏c) (eval-pt-isIso 𝟏c)
    ( comp-assoc eval-pt eval-pt-inv 𝕀₀
    ∙ ap (λ m → comp m 𝕀₀) eval-pt-rinv
    ∙ comp-id-l 𝕀₀
    ∙ eval-pt-dom-last ⁻¹ )

------------------------------------------------------------------------
-- The cone ↔ composable-pair reshuffle (Rocq `reshuffle`/`psi`)
--
-- An honest equivalence (no `is-set (Ob X)` needed): the base is reindexed
-- by the eval-pt iso, and the coherence path-types are matched by composing
-- with fixed paths (`pre/post-comp-path-equiv`).
------------------------------------------------------------------------

-- precomposition by the iso eval-pt-inv : 𝕀 → Δ¹ is an equivalence
-- forward kept transparent (its value is needed); is-equiv kept opaque.
precomp-eval-fwd : (X : Cat) → Map (Δ (suc zero)) X → Mor X
precomp-eval-fwd X g = comp g eval-pt-inv

opaque
  precomp-eval-ie : (X : Cat) → is-equiv (precomp-eval-fwd X)
  precomp-eval-ie X =
    invertible-to-equiv _
      ((λ f → comp f eval-pt) ,
       (λ f → composeA f eval-pt eval-pt-inv
            ∙ ap (comp f) eval-pt-rinv ∙ comp-id-r f) ,
       (λ g → composeA g eval-pt-inv eval-pt
            ∙ ap (comp g) eval-pt-linv ∙ comp-id-r g))

precomp-eval-equiv : (X : Cat) → Map (Δ (suc zero)) X ≃ Mor X
precomp-eval-equiv X = precomp-eval-fwd X , precomp-eval-ie X

-- The reshuffle pieces, lifted to module level so the reshuffle-comparison
-- proof can name them (they were a `where`-block before).
private
  cp-coh : {X : Cat} → (Mor X × Mor X) → Type 𝓤₀
  cp-coh fg = cod (pr₁ fg) ≡ dom (pr₂ fg)

  cp-b : (X : Cat) → (Map (Δ (suc zero)) X × Map (Δ (suc zero)) X) ≃ (Mor X × Mor X)
  cp-b X = ×-equiv (precomp-eval-equiv X) (precomp-eval-equiv X)

  -- cod/dom of the eval-reindexed map ARE the two simplex vertices.
  lhsf : {X : Cat} (g : Map (Δ (suc zero)) X) → cod (comp g eval-pt-inv) ≡ comp g (top (suc zero))
  lhsf g = composeA g eval-pt-inv 𝕀₁ ∙ ap (comp g) ei1

  rhsf : {X : Cat} (e : Map (Δ (suc zero)) X) → dom (comp e eval-pt-inv) ≡ comp e v0-Δ1
  rhsf e = composeA e eval-pt-inv 𝕀₀ ∙ ap (comp e) ei0

  -- forward EXPLICIT (so `pr₁ (cp-fiber …)` reduces syntactically, not by
  -- unfolding the equiv-comp — that unfolding cost ~37 s); is-equiv opaque.
  cp-fiber-fwd : (X : Cat) (g e : Map (Δ (suc zero)) X)
    → (comp g (top (suc zero)) ≡ comp e v0-Δ1) → cod (comp g eval-pt-inv) ≡ dom (comp e eval-pt-inv)
  cp-fiber-fwd X g e c =
    pr₁ (post-comp-path-equiv (rhsf e ⁻¹)) (pr₁ (pre-comp-path-equiv (lhsf g)) c)

  opaque
    cp-fiber-ie : (X : Cat) (g e : Map (Δ (suc zero)) X) → is-equiv (cp-fiber-fwd X g e)
    cp-fiber-ie X g e =
      pr₂ (equiv-comp (pre-comp-path-equiv (lhsf g)) (post-comp-path-equiv (rhsf e ⁻¹)))

  cp-fiber : (X : Cat) (ge : Map (Δ (suc zero)) X × Map (Δ (suc zero)) X)
    → (comp (pr₁ ge) (top (suc zero)) ≡ comp (pr₂ ge) v0-Δ1) ≃ cp-coh (pr₁ (cp-b X) ge)
  cp-fiber X (g , e) = cp-fiber-fwd X g e , cp-fiber-ie X g e

  cp-curry : (X : Cat) → (Σ fg ꞉ (Mor X × Mor X) , cp-coh fg) ≃ ComposablePair X
  cp-curry X =
    (λ w → pr₁ (pr₁ w) , pr₂ (pr₁ w) , pr₂ w) ,
    invertible-to-equiv _
      ((λ w → (pr₁ w , pr₁ (pr₂ w)) , pr₂ (pr₂ w)) ,
       (λ _ → refl _) , (λ _ → refl _))

-- The forward map, given EXPLICITLY (so it reduces in one step, instead of
-- unfolding the whole equivalence composite — that unfolding cost ~38 s).
-- The heavy `is-equiv` half is kept `opaque`, the documented opacity trick.
cpf : (X : Cat) → sq-cone (Sq (suc zero)) X → ComposablePair X
cpf X ((g , e) , coh) =
  comp g eval-pt-inv , comp e eval-pt-inv , pr₁ (cp-fiber X (g , e)) coh

opaque
  cpf-is-equiv : (X : Cat) → is-equiv (cpf X)
  cpf-is-equiv X =
    pr₂ (equiv-comp (Σ-fiberwise-equiv (cp-fiber X))
           (equiv-comp (Σ-change-of-base (cp-b X)) (cp-curry X)))

cone-pair-equiv : (X : Cat) → sq-cone (Sq (suc zero)) X ≃ ComposablePair X
cone-pair-equiv X = cpf X , cpf-is-equiv X

------------------------------------------------------------------------
-- reshuffle-comparison (Rocq `psi_comparison`, Main.v 5684), PROVED.
--
-- pr₁ (cone-pair-equiv X) ∘ sq-comparison (Sq 1) ≡ segal-comparison.
-- The forward map computes (`cone-pair-fwd`); the two ComposablePairs then
-- agree componentwise (`CP-≡`): the morphisms by the coface bridge, and the
-- coherence 2-cell by the fact that `Ob (Δ 2)` is a SET (Δ² posetal), so the
-- two coherence proofs — both paths between the same two Δ²-vertices — are
-- equal once the iso/coface scaffolding is stripped.
------------------------------------------------------------------------

-- the two path-action equivalences compute to ∙.
pre-comp-compute : {A : Type 𝓤} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → pr₁ (pre-comp-path-equiv p) q ≡ p ∙ q
pre-comp-compute (refl _) q = refl q

post-comp-compute : {A : Type 𝓤} {x y z : A} (q : y ≡ z) (p : x ≡ y)
  → pr₁ (post-comp-path-equiv q) p ≡ p ∙ q
post-comp-compute (refl _) p = (right-unit p) ⁻¹

-- The cp-fiber value, as a formula over ABSTRACT paths.  Proving it here (l,
-- c, r are variables) keeps the heavy `eval-pt-inv` out of implicit-argument
-- inference; applying it to the real paths then never re-normalizes them.
-- (Inlining this instead cost ~37 s — the missing abstraction.)
fib-formula : {A : Type 𝓤} {x y z w : A} (l : x ≡ y) (c : y ≡ w) (r : z ≡ w)
  → pr₁ (post-comp-path-equiv (r ⁻¹)) (pr₁ (pre-comp-path-equiv l) c)
    ≡ (l ∙ c) ∙ r ⁻¹
fib-formula l c r =
    post-comp-compute (r ⁻¹) (pr₁ (pre-comp-path-equiv l) c)
  ∙ ap (λ w → w ∙ r ⁻¹) (pre-comp-compute l c)

-- the explicit value of cone-pair-equiv's forward map on a cone.
cone-pair-fwd : (X : Cat) (g e : Map (Δ (suc zero)) X)
  (coh : comp g (top (suc zero)) ≡ comp e v0-Δ1)
  → pr₁ (cone-pair-equiv X) ((g , e) , coh)
    ≡ (comp g eval-pt-inv , comp e eval-pt-inv , (lhsf g ∙ coh) ∙ (rhsf e) ⁻¹)
cone-pair-fwd X g e coh =
  ap (λ z → comp g eval-pt-inv , comp e eval-pt-inv , z)
     (fib-formula (lhsf g) coh (rhsf e))

-- equality of composable pairs from componentwise data.
CP-≡ : {X : Cat} {f f' g g' : Mor X}
       (pf : f ≡ f') (pg : g ≡ g')
       (c : cod f ≡ dom g) (c' : cod f' ≡ dom g')
     → c ∙ ap dom pg ≡ ap cod pf ∙ c'
     → (f , g , c) ≡ (f' , g' , c')
CP-≡ {X} {f} {f} {g} {g} (refl _) (refl _) c c' r =
  ap (λ z → f , g , z) ((right-unit c) ⁻¹ ∙ r)

-- The two Δ²-vertex bridges: `cod d₀₁` / `dom d₁₂` are the two simplex
-- vertices `comp (face 1) (top 1)` / `comp (lastedge 1) v0-Δ1`.
μ-Δ2 : cod d₀₁ ≡ comp (face (suc zero)) (top (suc zero))
μ-Δ2 = ap (λ m → comp m 𝕀₁) segal-coface-01
     ∙ composeA (face (suc zero)) eval-pt-inv 𝕀₁
     ∙ ap (comp (face (suc zero))) ei1

ν-Δ2 : dom d₁₂ ≡ comp (lastedge (suc zero)) v0-Δ1
ν-Δ2 = ap (λ m → comp m 𝕀₀) segal-coface-12
     ∙ composeA (lastedge (suc zero)) eval-pt-inv 𝕀₀
     ∙ ap (comp (lastedge (suc zero))) ei0

-- THE CONTENT: the postulated Segal coherence and the geometric square's
-- commutativity are equal — both are paths between the same two vertices of
-- the SET `Ob (Δ 2)` (Δ² is posetal).  This is the only non-structural step.
content : segal-comm ≡ μ-Δ2 ∙ (square-commutes (suc zero)) ⁻¹ ∙ ν-Δ2 ⁻¹
content =
  ob-Δ-is-set (suc (suc zero)) (cod d₀₁) (dom d₁₂)
    segal-comm (μ-Δ2 ∙ (square-commutes (suc zero)) ⁻¹ ∙ ν-Δ2 ⁻¹)

-- The "before" coherence (left of the shared `ap (comp h) sc1⁻¹`): an
-- instance of the Mac Lane pentagon, once the coface/iso paths are induced
-- to refl.
lemB-gen : {X : Cat} (h : Map (Δ (suc (suc zero))) X)
   (d : Mor (Δ (suc (suc zero)))) (cf : d ≡ comp (face (suc zero)) eval-pt-inv)
   (t : Ob (Δ (suc zero))) (e1 : comp eval-pt-inv 𝕀₁ ≡ t)
  → (composeA (comp h (face (suc zero))) eval-pt-inv 𝕀₁ ∙ ap (comp (comp h (face (suc zero)))) e1)
      ∙ composeA h (face (suc zero)) t
  ≡ ap cod (composeA h (face (suc zero)) eval-pt-inv ∙ ap (comp h) (cf ⁻¹))
      ∙ composeA h d 𝕀₁
      ∙ ap (comp h) ( ap (λ m → comp m 𝕀₁) cf
                      ∙ composeA (face (suc zero)) eval-pt-inv 𝕀₁
                      ∙ ap (comp (face (suc zero))) e1 )
lemB-gen h .(comp (face (suc zero)) eval-pt-inv) (refl _) .(comp eval-pt-inv 𝕀₁) (refl _) =
    ap (λ z → z ∙ composeA h (face (suc zero)) (comp eval-pt-inv 𝕀₁))
       (right-unit (composeA (comp h (face (suc zero))) eval-pt-inv 𝕀₁))
  ∙ pentagonator h (face (suc zero)) eval-pt-inv 𝕀₁
  ∙ ∙-cong
      (∙-cong ((ap-∙ cod P1 (refl _) ∙ right-unit (ap cod P1)) ⁻¹)
              (refl (composeA h (comp (face (suc zero)) eval-pt-inv) 𝕀₁)))
      ((ap-∙ (comp h) P2 (refl _) ∙ right-unit (ap (comp h) P2)) ⁻¹)
  where
  P1 = composeA h (face (suc zero)) eval-pt-inv
  P2 = composeA (face (suc zero)) eval-pt-inv 𝕀₁

-- The non-inverted "after" pentagon (mirror of lemB-gen for lastedge/𝕀₀/dom).
lemA0-gen : {X : Cat} (h : Map (Δ (suc (suc zero))) X)
   (d : Mor (Δ (suc (suc zero)))) (cg : d ≡ comp (lastedge (suc zero)) eval-pt-inv)
   (s : Ob (Δ (suc zero))) (e0 : comp eval-pt-inv 𝕀₀ ≡ s)
  → (composeA (comp h (lastedge (suc zero))) eval-pt-inv 𝕀₀ ∙ ap (comp (comp h (lastedge (suc zero)))) e0)
      ∙ composeA h (lastedge (suc zero)) s
  ≡ ap dom (composeA h (lastedge (suc zero)) eval-pt-inv ∙ ap (comp h) (cg ⁻¹))
      ∙ composeA h d 𝕀₀
      ∙ ap (comp h) ( ap (λ m → comp m 𝕀₀) cg
                      ∙ composeA (lastedge (suc zero)) eval-pt-inv 𝕀₀
                      ∙ ap (comp (lastedge (suc zero))) e0 )
lemA0-gen h .(comp (lastedge (suc zero)) eval-pt-inv) (refl _) .(comp eval-pt-inv 𝕀₀) (refl _) =
    ap (λ z → z ∙ composeA h (lastedge (suc zero)) (comp eval-pt-inv 𝕀₀))
       (right-unit (composeA (comp h (lastedge (suc zero))) eval-pt-inv 𝕀₀))
  ∙ pentagonator h (lastedge (suc zero)) eval-pt-inv 𝕀₀
  ∙ ∙-cong
      (∙-cong ((ap-∙ dom Q1 (refl _) ∙ right-unit (ap dom Q1)) ⁻¹)
              (refl (composeA h (comp (lastedge (suc zero)) eval-pt-inv) 𝕀₀)))
      ((ap-∙ (comp h) Q2 (refl _) ∙ right-unit (ap (comp h) Q2)) ⁻¹)
  where
  Q1 = composeA h (lastedge (suc zero)) eval-pt-inv
  Q2 = composeA (lastedge (suc zero)) eval-pt-inv 𝕀₀

big2 : (X : Cat) (h : Map (Δ (suc (suc zero))) X)
    → ((lhsf (comp h (face (suc zero))) ∙ pr₂ (sq-comparison (Sq (suc zero)) X h))
        ∙ (rhsf (comp h (lastedge (suc zero)))) ⁻¹)
       ∙ ap dom (composeA h (lastedge (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-12 ⁻¹))
     ≡ ap cod (composeA h (face (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-01 ⁻¹))
       ∙ pr₂ (pr₂ (segal-comparison X h))
big2 X h = e1 ∙ e2 ∙ e34
  where
  g₀ = comp h (face (suc zero))
  e₀ = comp h (lastedge (suc zero))
  S  = ap (comp h) (square-commutes (suc zero) ⁻¹)
  Pf = composeA h (face (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-01 ⁻¹)
  Pg = composeA h (lastedge (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-12 ⁻¹)
  C  = composeA h (lastedge (suc zero)) v0-Δ1
  -- the pieces (left / right of the shared S = ap(comp h)(sc1⁻¹))
  LB = lhsf g₀ ∙ composeA h (face (suc zero)) (top (suc zero))
  RB = ap cod Pf ∙ composeA h d₀₁ 𝕀₁ ∙ ap (comp h) μ-Δ2
  RA = (C ⁻¹ ∙ (rhsf e₀) ⁻¹) ∙ ap dom Pg
  RA' = ap (comp h) (ν-Δ2 ⁻¹) ∙ (composeA h d₁₂ 𝕀₀) ⁻¹

  lemB : LB ≡ RB
  lemB = lemB-gen h d₀₁ segal-coface-01 (top (suc zero)) ei1

  -- the inverted "after" half, from lemA0-gen.
  lemA0 : (rhsf e₀ ∙ C) ≡ ap dom Pg ∙ composeA h d₁₂ 𝕀₀ ∙ ap (comp h) ν-Δ2
  lemA0 = lemA0-gen h d₁₂ segal-coface-12 v0-Δ1 ei0

  lemA : RA ≡ RA'
  lemA =
      ap (λ z → z ∙ ap dom Pg)
         ( solveG (inv (ι C) ⊕ inv (ι (rhsf e₀))) (inv (ι (rhsf e₀) ⊕ ι C)) (refl _)
         ∙ ap _⁻¹ lemA0
         ∙ solveG (inv ((ι (ap dom Pg) ⊕ ι (composeA h d₁₂ 𝕀₀)) ⊕ ι (ap (comp h) ν-Δ2)))
                  ((inv (ι (ap (comp h) ν-Δ2)) ⊕ inv (ι (composeA h d₁₂ 𝕀₀))) ⊕ inv (ι (ap dom Pg)))
                  (refl _) )
    ∙ solveG ((( inv (ι (ap (comp h) ν-Δ2)) ⊕ inv (ι (composeA h d₁₂ 𝕀₀))) ⊕ inv (ι (ap dom Pg))) ⊕ ι (ap dom Pg))
             (( inv (ι (ap (comp h) ν-Δ2)) ⊕ inv (ι (composeA h d₁₂ 𝕀₀))) ⊕ (inv (ι (ap dom Pg)) ⊕ ι (ap dom Pg)))
             (refl _)
    ∙ ap (λ z → ((ap (comp h) ν-Δ2) ⁻¹ ∙ (composeA h d₁₂ 𝕀₀) ⁻¹) ∙ z) (left-inv (ap dom Pg))
    ∙ right-unit ((ap (comp h) ν-Δ2) ⁻¹ ∙ (composeA h d₁₂ 𝕀₀) ⁻¹)
    ∙ ap (λ z → z ∙ (composeA h d₁₂ 𝕀₀) ⁻¹) ((ap-⁻¹ (comp h) ν-Δ2) ⁻¹)

  -- e1 : LHS ≡ LB ∙ S ∙ RA   (reassociation only)
  e1 : ((lhsf g₀ ∙ pr₂ (sq-comparison (Sq (suc zero)) X h)) ∙ (rhsf e₀) ⁻¹) ∙ ap dom Pg
     ≡ (LB ∙ S) ∙ RA
  e1 = solveG
        (((ι (lhsf g₀) ⊕ ((ι (composeA h (face (suc zero)) (top (suc zero))) ⊕ ι S) ⊕ inv (ι C)))
            ⊕ inv (ι (rhsf e₀))) ⊕ ι (ap dom Pg))
        (((ι (lhsf g₀) ⊕ ι (composeA h (face (suc zero)) (top (suc zero)))) ⊕ ι S)
            ⊕ ((inv (ι C) ⊕ inv (ι (rhsf e₀))) ⊕ ι (ap dom Pg)))
        (refl _)

  e2 : (LB ∙ S) ∙ RA ≡ (RB ∙ S) ∙ RA'
  e2 = ∙-cong (∙-cong lemB (refl S)) lemA

  -- e34 : (RB ∙ S) ∙ RA' ≡ RHS   (reassoc + ap-∙ + content)
  expandStep : ap (comp h) (μ-Δ2 ∙ square-commutes (suc zero) ⁻¹ ∙ ν-Δ2 ⁻¹)
             ≡ (ap (comp h) μ-Δ2 ∙ S) ∙ ap (comp h) (ν-Δ2 ⁻¹)
  expandStep =
      ap-∙ (comp h) (μ-Δ2 ∙ square-commutes (suc zero) ⁻¹) (ν-Δ2 ⁻¹)
    ∙ ap (λ z → z ∙ ap (comp h) (ν-Δ2 ⁻¹)) (ap-∙ (comp h) μ-Δ2 (square-commutes (suc zero) ⁻¹))

  e34 : (RB ∙ S) ∙ RA' ≡ ap cod Pf ∙ pr₂ (pr₂ (segal-comparison X h))
  e34 =
      solveG
        ((((ι (ap cod Pf) ⊕ ι (composeA h d₀₁ 𝕀₁)) ⊕ ι (ap (comp h) μ-Δ2)) ⊕ ι S)
           ⊕ (ι (ap (comp h) (ν-Δ2 ⁻¹)) ⊕ inv (ι (composeA h d₁₂ 𝕀₀))))
        (ι (ap cod Pf) ⊕ ((ι (composeA h d₀₁ 𝕀₁)
           ⊕ ((ι (ap (comp h) μ-Δ2) ⊕ ι S) ⊕ ι (ap (comp h) (ν-Δ2 ⁻¹))))
           ⊕ inv (ι (composeA h d₁₂ 𝕀₀))))
        (refl _)
    ∙ ap (λ z → ap cod Pf ∙ (composeA h d₀₁ 𝕀₁ ∙ z ∙ (composeA h d₁₂ 𝕀₀) ⁻¹))
         (expandStep ⁻¹)
    ∙ ap (λ w → ap cod Pf ∙ (composeA h d₀₁ 𝕀₁ ∙ ap (comp h) w ∙ (composeA h d₁₂ 𝕀₀) ⁻¹))
         (content ⁻¹)

reshuffle-comparison : (X : Cat) (h : Map (Δ (suc (suc zero))) X)
    → pr₁ (cone-pair-equiv X) (sq-comparison (Sq (suc zero)) X h) ≡ segal-comparison X h
reshuffle-comparison X h =
    cone-pair-fwd X (comp h (face (suc zero))) (comp h (lastedge (suc zero)))
                    (pr₂ (sq-comparison (Sq (suc zero)) X h))
  ∙ CP-≡ (composeA h (face (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-01 ⁻¹))
         (composeA h (lastedge (suc zero)) eval-pt-inv ∙ ap (comp h) (segal-coface-12 ⁻¹))
         ((lhsf (comp h (face (suc zero))) ∙ pr₂ (sq-comparison (Sq (suc zero)) X h))
           ∙ (rhsf (comp h (lastedge (suc zero)))) ⁻¹)
         (pr₂ (pr₂ (segal-comparison X h)))
         (big2 X h)

------------------------------------------------------------------------
-- base-Sq1 : Sq 1 is a pushout  (Rocq `base_Sq1`, Main.v 5736), DERIVED
-- from the Segal axiom by the reshuffle.
------------------------------------------------------------------------

base-Sq1 : is-pushout-square (Sq (suc zero))
base-Sq1 X = homotopic-is-equiv htpy (pr₂ g₀-equiv)
  where
    g₀-equiv : Map (Δ (suc (suc zero))) X ≃ sq-cone (Sq (suc zero)) X
    g₀-equiv = equiv-comp (segal-equiv X) (≃-sym (cone-pair-equiv X))
    htpy : (h : Map (Δ (suc (suc zero))) X)
         → equiv-inv (cone-pair-equiv X) (segal-comparison X h)
           ≡ sq-comparison (Sq (suc zero)) X h
    htpy h =
      ap (equiv-inv (cone-pair-equiv X)) (reshuffle-comparison X h ⁻¹)
      ∙ equiv-inv-linv (cone-pair-equiv X) (sq-comparison (Sq (suc zero)) X h)
