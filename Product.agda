{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Stage 4: the product pentagon `prod_pent_C`.
--
-- Port of the LUCIE Rocq development (Main.v product section, pmc.v,
-- pp_C.v, dsl_C.v) onto the correct, `map-is-set`-free axiom base.
--
-- The product is the binary product `_×c_` from Pullbacks; `injl`/`injr`
-- are its projections.  `product-map` is the functorial action of `(−×−)`;
-- `pmc` is the multiplicativity comparison; `prod-path-eq` is the
-- cell-level pairing-uniqueness principle.  The two factor proofs
-- (`prod-pent-C-injl` / `prod-pent-C-injr`) are then assembled by
-- `prod-path-eq` into `prod-pent-C`.
------------------------------------------------------------------------

module Product where

open import Spartan
open import CatAxioms
open import HigherCat
open import Constructions
open import Pullbacks
open import Interval using (invertible-to-equiv)
open import Coherence
open import PastingDSL
open import Normaliser
open import CayleyAssoc
open import PastingTest using (injr-unit-loop)

------------------------------------------------------------------------
-- §0  Foundational path-algebra helpers (non-dependent product paths,
--     equiv-inj projection law, retract path-injectivity).
------------------------------------------------------------------------

-- Paths in a (non-dependent) product, reconstructed from the two factors.
pair⁼ : {A : Type 𝓤} {B : Type 𝓥} {a a' : A} {b b' : B}
      → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
pair⁼ (refl _) (refl _) = refl _

pair⁼-β₁ : {A : Type 𝓤} {B : Type 𝓥} {a a' : A} {b b' : B}
           (s : a ≡ a') (t : b ≡ b')
         → ap pr₁ (pair⁼ s t) ≡ s
pair⁼-β₁ (refl _) (refl _) = refl _

pair⁼-β₂ : {A : Type 𝓤} {B : Type 𝓥} {a a' : A} {b b' : B}
           (s : a ≡ a') (t : b ≡ b')
         → ap pr₂ (pair⁼ s t) ≡ t
pair⁼-β₂ (refl _) (refl _) = refl _

pair⁼-η : {A : Type 𝓤} {B : Type 𝓥} {w w' : A × B} (α : w ≡ w')
        → pair⁼ (ap pr₁ α) (ap pr₂ α) ≡ α
pair⁼-η (refl _) = refl _

-- Two product paths with equal projections are equal.
prod-path-uniq : {A : Type 𝓤} {B : Type 𝓥} {w w' : A × B} (α β : w ≡ w')
               → ap pr₁ α ≡ ap pr₁ β → ap pr₂ α ≡ ap pr₂ β → α ≡ β
prod-path-uniq α β Hl Hr =
    (pair⁼-η α) ⁻¹
  ∙ ap2-pair⁼ Hl Hr
  ∙ pair⁼-η β
  where
  ap2-pair⁼ : {A : Type 𝓤} {B : Type 𝓥} {a a' : A} {b b' : B}
              {s s' : a ≡ a'} {t t' : b ≡ b'}
            → s ≡ s' → t ≡ t' → pair⁼ s t ≡ pair⁼ s' t'
  ap2-pair⁼ (refl _) (refl _) = refl _

-- For σ a path in a fiber, the action of (f ∘ pr₁) on σ followed by the
-- target witness recovers the source witness.
fiber-ap : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {b : B}
           {w₀ w₁ : Σ a ꞉ A , f a ≡ b} (σ : w₀ ≡ w₁)
         → ap (λ w → f (pr₁ w)) σ ∙ pr₂ w₁ ≡ pr₂ w₀
fiber-ap f (refl _) = refl _

-- The projection law for `equiv-inj`: applying f back recovers the path.
mp-equiv-inj : {A B : Type 𝓤} (f : A → B) (ef : is-equiv f)
               {x y : A} (q : f x ≡ f y)
             → ap f (equiv-inj f ef q) ≡ q
mp-equiv-inj f ef {x} {y} q =
    ap-comp f pr₁ σ ∙ recover
  where
  σ : (x , refl (f x)) ≡ (y , q ⁻¹)
  σ = singletons-are-props (ef (f x)) (x , refl (f x)) (y , q ⁻¹)
  -- ap (f ∘ pr₁) σ ∙ q ⁻¹ ≡ refl (f x)
  H : ap (λ w → f (pr₁ w)) σ ∙ q ⁻¹ ≡ refl (f x)
  H = fiber-ap f σ
  recover : ap (λ w → f (pr₁ w)) σ ≡ q
  recover =
      (right-unit _) ⁻¹
    ∙ ap (λ z → ap (λ w → f (pr₁ w)) σ ∙ z) ((left-inv q) ⁻¹)
    ∙ (∙-assoc (ap (λ w → f (pr₁ w)) σ) (q ⁻¹) q) ⁻¹
    ∙ ap (λ z → z ∙ q) H

-- A map with a retraction is injective on paths.
retract-path-inj : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) (r : B → A)
                   (η : (a : A) → r (f a) ≡ a)
                   {x y : A} (p p' : x ≡ y)
                 → ap f p ≡ ap f p' → p ≡ p'
retract-path-inj f r η {x} {y} p p' e =
    recover p ∙ ap (λ z → η x ⁻¹ ∙ (z ∙ η y)) E ∙ (recover p') ⁻¹
  where
  recover : (p : x ≡ y) → p ≡ η x ⁻¹ ∙ (ap (λ a → r (f a)) p ∙ η y)
  recover (refl _) = (left-inv (η x)) ⁻¹
  E : ap (λ a → r (f a)) p ≡ ap (λ a → r (f a)) p'
  E = (ap-comp r f p) ⁻¹ ∙ ap (ap r) e ∙ ap-comp r f p'

------------------------------------------------------------------------
-- §1  product, injl, injr
------------------------------------------------------------------------

product : Cat → Cat → Cat
product = _×c_

injl : {A B : Cat} → Map (A ×c B) A
injl {A} {B} = π₁ A B

injr : {A B : Cat} → Map (A ×c B) B
injr {A} {B} = π₂ A B

------------------------------------------------------------------------
-- §2  product-map and its projections
------------------------------------------------------------------------

-- `product-map` (and its two projection laws) are kept `opaque`: their
-- unfolding goes through `⟨_,_⟩` = `equiv-inv …`, a huge term.  Downstream
-- proofs only ever use the projection laws, so opacity keeps cell *types*
-- atomic and type-checking fast (Rocq trap b: "keep it opaque").
opaque
  product-map : {A B X Y : Cat} → Map A B → Map X Y → Map (A ×c X) (B ×c Y)
  product-map {A} {B} {X} {Y} f g = ⟨ comp f (π₁ A X) , comp g (π₂ A X) ⟩

  -- injl ∘ product-map f g ≡ f ∘ injl   (Rocq injl_product_map)
  injl-product-map : {A B X Y : Cat} (f : Map A B) (g : Map X Y)
                   → comp injl (product-map f g) ≡ comp f injl
  injl-product-map {A} {B} {X} {Y} f g = pair-β₁ (comp f (π₁ A X)) (comp g (π₂ A X))

  -- injr ∘ product-map f g ≡ g ∘ injr   (Rocq injr_product_map)
  injr-product-map : {A B X Y : Cat} (f : Map A B) (g : Map X Y)
                   → comp injr (product-map f g) ≡ comp g injr
  injr-product-map {A} {B} {X} {Y} f g = pair-β₂ (comp f (π₁ A X)) (comp g (π₂ A X))

------------------------------------------------------------------------
-- §3  product-map-eq1 / product-map-eq2
------------------------------------------------------------------------

product-map-eq1 : {A B X Y : Cat} {f f' : Map A B} (g : Map X Y)
                → f ≡ f' → product-map f g ≡ product-map f' g
product-map-eq1 g p = ap (λ f → product-map f g) p

product-map-eq2 : {A B X Y : Cat} (f : Map A B) {g g' : Map X Y}
                → g ≡ g' → product-map f g ≡ product-map f g'
product-map-eq2 f p = ap (λ g → product-map f g) p

------------------------------------------------------------------------
-- §4a  The product-comparison is an equivalence; the path-into-product
--      principle `ipe` with computable projections.
------------------------------------------------------------------------

prod-comp-equiv : (A B X : Cat) → is-equiv (prod-comparison A B X)
prod-comp-equiv A B X =
  invertible-to-equiv (prod-comparison A B X)
    (prod-section A B X , prod-roundtrip A B X , pair-η)

-- `ipe` and its projection laws are kept `opaque` (their unfolding goes
-- through `equiv-inj`/`prod-comp-equiv`, again huge); downstream only the
-- two projection laws are used.
opaque
  -- Build a path into a product from its two projections (Rocq `ipe`).
  ipe : {A B D : Cat} (f g : Map D (A ×c B))
      → comp injl f ≡ comp injl g → comp injr f ≡ comp injr g → f ≡ g
  ipe {A} {B} {D} f g el er =
    equiv-inj (prod-comparison A B D) (prod-comp-equiv A B D) (pair⁼ el er)

  -- Projection laws for ipe (Rocq `ipe_injl` / `ipe_injr`).
  ipe-injl : {A B D : Cat} (f g : Map D (A ×c B))
             (el : comp injl f ≡ comp injl g) (er : comp injr f ≡ comp injr g)
           → ccr injl (ipe f g el er) ≡ el
  ipe-injl {A} {B} {D} f g el er =
      ap-comp pr₁ (prod-comparison A B D) (ipe f g el er) ⁻¹
    ∙ ap (ap pr₁) (mp-equiv-inj (prod-comparison A B D) (prod-comp-equiv A B D) (pair⁼ el er))
    ∙ pair⁼-β₁ el er

  ipe-injr : {A B D : Cat} (f g : Map D (A ×c B))
             (el : comp injl f ≡ comp injl g) (er : comp injr f ≡ comp injr g)
           → ccr injr (ipe f g el er) ≡ er
  ipe-injr {A} {B} {D} f g el er =
      ap-comp pr₂ (prod-comparison A B D) (ipe f g el er) ⁻¹
    ∙ ap (ap pr₂) (mp-equiv-inj (prod-comparison A B D) (prod-comp-equiv A B D) (pair⁼ el er))
    ∙ pair⁼-β₂ el er

------------------------------------------------------------------------
-- §4b  prod-path-eq: cell-level pairing uniqueness (Rocq `prod_path_eq`).
------------------------------------------------------------------------

prod-path-eq : {A B X : Cat} {F F' : Map X (A ×c B)} (p q : F ≡ F')
             → ccr injl p ≡ ccr injl q → ccr injr p ≡ ccr injr q → p ≡ q
prod-path-eq {A} {B} {X} {F} {F'} p q Hl Hr =
  retract-path-inj (prod-comparison A B X) (prod-section A B X) pair-η p q
    (prod-path-uniq (ap (prod-comparison A B X) p) (ap (prod-comparison A B X) q)
      (projl p ∙ Hl ∙ projl q ⁻¹)
      (projr p ∙ Hr ∙ projr q ⁻¹))
  where
  projl : (p : F ≡ F') → ap pr₁ (ap (prod-comparison A B X) p) ≡ ccr injl p
  projl p = ap-comp pr₁ (prod-comparison A B X) p
  projr : (p : F ≡ F') → ap pr₂ (ap (prod-comparison A B X) p) ≡ ccr injr p
  projr p = ap-comp pr₂ (prod-comparison A B X) p

------------------------------------------------------------------------
-- §4c  pmc: the multiplicativity comparison (Rocq `pmc`), built by `ipe`
--      so its two projections compute (Rocq `pmc_injl` / `pmc_injr`).
------------------------------------------------------------------------

module _ {XX Y Z A B C : Cat} (f : Map Z Y) (g : Map Y XX) (i : Map C B) (j : Map B A) where

  -- the injl leg of pmc
  pmc-legl : comp injl (product-map (comp g f) (comp j i))
           ≡ comp injl (comp (product-map g j) (product-map f i))
  pmc-legl =
      injl-product-map (comp g f) (comp j i)
    ∙ composeA g f injl
    ∙ ccr g (injl-product-map f i ⁻¹)
    ∙ composeA g injl (product-map f i) ⁻¹
    ∙ ccl (product-map f i) (injl-product-map g j ⁻¹)
    ∙ composeA injl (product-map g j) (product-map f i)

  -- the injr leg of pmc
  pmc-legr : comp injr (product-map (comp g f) (comp j i))
           ≡ comp injr (comp (product-map g j) (product-map f i))
  pmc-legr =
      injr-product-map (comp g f) (comp j i)
    ∙ composeA j i injr
    ∙ ccr j (injr-product-map f i ⁻¹)
    ∙ composeA j injr (product-map f i) ⁻¹
    ∙ ccl (product-map f i) (injr-product-map g j ⁻¹)
    ∙ composeA injr (product-map g j) (product-map f i)

  -- `pmc` opaque (it is `ipe …`, kept opaque downstream — Rocq trap b);
  -- only its two projections are ever used.
  opaque
    pmc : product-map (comp g f) (comp j i)
        ≡ comp (product-map g j) (product-map f i)
    pmc = ipe _ _ pmc-legl pmc-legr

    pmc-injl : ccr injl pmc ≡ pmc-legl
    pmc-injl = ipe-injl _ _ pmc-legl pmc-legr

    pmc-injr : ccr injr pmc ≡ pmc-legr
    pmc-injr = ipe-injr _ _ pmc-legl pmc-legr

------------------------------------------------------------------------
-- §4d  CPS collapse lemmas (Rocq pp_C.v `cn1_n`, `cn2_collapse`,
--      `cn3_collapse`, `nat3_cps`, `pent_expand`, `pent_cps`).
--      The pure path-induction ones close by `refl` because every
--      vanishing cell lands on the LEFT of `∙` (Agda-definitional).
------------------------------------------------------------------------

cn1-n : {AA BB CC DD : Cat} {f f' : Map CC DD} (gg : Map BB CC) (hh : Map AA BB)
        (F : f ≡ f') {Z : Map AA DD} (rest : comp f' (comp gg hh) ≡ Z)
      → ccl hh (ccl gg F) ∙ (composeA f' gg hh ∙ rest)
      ≡ composeA f gg hh ∙ (ccl (comp gg hh) F ∙ rest)
cn1-n gg hh (refl _) rest = refl _

cn3-collapse : {AA BB CC DD : Cat} (f : Map CC DD) (gg : Map BB CC)
               {hh hh' : Map AA BB} (F : hh ≡ hh') {Z : Map AA DD}
               (rest : comp f (comp gg hh') ≡ Z)
             → ccr (comp f gg) (F ⁻¹)
                 ∙ (composeA f gg hh ∙ (ccr f (ccr gg F) ∙ rest))
             ≡ composeA f gg hh' ∙ rest
cn3-collapse f gg (refl _) rest = refl _

cn2-collapse : {AA BB CC DD : Cat} (f : Map CC DD) {gg gg' : Map BB CC}
               (hh : Map AA BB) (F : gg ≡ gg') {Z : Map AA DD}
               (rest : comp f (comp gg' hh) ≡ Z)
             → ccl hh (ccr f (F ⁻¹))
                 ∙ (composeA f gg hh ∙ (ccr f (ccl hh F) ∙ rest))
             ≡ composeA f gg' hh ∙ rest
cn2-collapse f hh (refl _) rest = refl _

nat3-cps : {AA BB CC DD : Cat} (f : Map CC DD) (gg : Map BB CC)
           {hh hh' : Map AA BB} (F : hh ≡ hh') {Z : Map AA DD}
           (rest : comp f (comp gg hh') ≡ Z)
         → composeA f gg hh ∙ (ccr f (ccr gg F) ∙ rest)
         ≡ ccr (comp f gg) F ∙ (composeA f gg hh' ∙ rest)
nat3-cps f gg (refl _) rest = refl _

pent-expand : {AA BB CC DD EE : Cat} (f : Map DD EE) (gg : Map CC DD)
              (hh : Map BB CC) (e : Map AA BB) {Z : Map AA EE}
              (rest : comp f (comp gg (comp hh e)) ≡ Z)
            → composeA (comp f gg) hh e ∙ (composeA f gg (comp hh e) ∙ rest)
            ≡ ccl e (composeA f gg hh)
                ∙ (composeA f (comp gg hh) e ∙ (ccr f (composeA gg hh e) ∙ rest))
pent-expand f gg hh e rest =
    (∙-assoc X1 X2 rest) ⁻¹
  ∙ ap (_∙ rest) (pentagonator f gg hh e)
  ∙ ∙-assoc (Y1 ∙ Y2) Y3 rest
  ∙ ∙-assoc Y1 Y2 (Y3 ∙ rest)
  where
  X1 = composeA (comp f gg) hh e
  X2 = composeA f gg (comp hh e)
  Y1 = ccl e (composeA f gg hh)
  Y2 = composeA f (comp gg hh) e
  Y3 = ccr f (composeA gg hh e)

pent-cps : {AA BB CC DD EE : Cat} (f : Map DD EE) (gg : Map CC DD)
           (hh : Map BB CC) (e : Map AA BB) {Z : Map AA EE}
           (rest : comp f (comp gg (comp hh e)) ≡ Z)
         → (composeA (comp f gg) hh e) ⁻¹
             ∙ (ccl e (composeA f gg hh)
                ∙ (composeA f (comp gg hh) e ∙ (ccr f (composeA gg hh e) ∙ rest)))
         ≡ composeA f gg (comp hh e) ∙ rest
pent-cps f gg hh e rest =
    ap (composeA (comp f gg) hh e ⁻¹ ∙_) ((pent-expand f gg hh e rest) ⁻¹)
  ∙ cancL (composeA (comp f gg) hh e) (composeA f gg (comp hh e) ∙ rest)

------------------------------------------------------------------------
-- Generic right-association helpers (turn a left-nested ∙-chain into the
-- canonical right-nested form, so adjacent inverse pairs become cancellable
-- by cancL/cancR).  Used by both factor collapses.
------------------------------------------------------------------------

module _ {A : Type 𝓤} where
  inv-∙ : {x y z : A} (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
  inv-∙ (refl _) q = (right-unit (q ⁻¹)) ⁻¹

  inv-inv : {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
  inv-inv (refl _) = refl _

  fa4 : {v w x y z : A} (a : v ≡ w) (b : w ≡ x) (c : x ≡ y) (d : y ≡ z)
      → ((a ∙ b) ∙ c) ∙ d ≡ a ∙ (b ∙ (c ∙ d))
  fa4 a b c d =
      ∙-assoc (a ∙ b) c d ∙ ∙-assoc a b (c ∙ d)

  fa5 : {u v w x y z : A} (a : u ≡ v) (b : v ≡ w) (c : w ≡ x) (d : x ≡ y) (e : y ≡ z)
      → (((a ∙ b) ∙ c) ∙ d) ∙ e ≡ a ∙ (b ∙ (c ∙ (d ∙ e)))
  fa5 a b c d e =
      ∙-assoc ((a ∙ b) ∙ c) d e ∙ fa4 a b c (d ∙ e)

  fa6 : {t u v w x y z : A}
        (a : t ≡ u) (b : u ≡ v) (c : v ≡ w) (d : w ≡ x) (e : x ≡ y) (f : y ≡ z)
      → ((((a ∙ b) ∙ c) ∙ d) ∙ e) ∙ f ≡ a ∙ (b ∙ (c ∙ (d ∙ (e ∙ f))))
  fa6 a b c d e f =
      ∙-assoc (((a ∙ b) ∙ c) ∙ d) e f ∙ fa5 a b c d (e ∙ f)

  fa7 : {s t u v w x y z : A}
        (a : s ≡ t) (b : t ≡ u) (c : u ≡ v) (d : v ≡ w) (e : w ≡ x) (f : x ≡ y) (G : y ≡ z)
      → (((((a ∙ b) ∙ c) ∙ d) ∙ e) ∙ f) ∙ G ≡ a ∙ (b ∙ (c ∙ (d ∙ (e ∙ (f ∙ G)))))
  fa7 a b c d e f G =
      ∙-assoc ((((a ∙ b) ∙ c) ∙ d) ∙ e) f G ∙ fa6 a b c d e (f ∙ G)

  -- inverse of a 6-fold left-nested chain, distributed to right-nested inverses
  invflat6 : {t u v w x y z : A}
             (a : t ≡ u) (b : u ≡ v) (c : v ≡ w) (d : w ≡ x) (e : x ≡ y) (f : y ≡ z)
           → (((((a ∙ b) ∙ c) ∙ d) ∙ e) ∙ f) ⁻¹
           ≡ f ⁻¹ ∙ (e ⁻¹ ∙ (d ⁻¹ ∙ (c ⁻¹ ∙ (b ⁻¹ ∙ a ⁻¹))))
  invflat6 a b c d e f =
      inv-∙ (((((a ∙ b) ∙ c) ∙ d) ∙ e)) f
    ∙ ap (f ⁻¹ ∙_) (inv-∙ ((((a ∙ b) ∙ c) ∙ d)) e
    ∙ ap (e ⁻¹ ∙_) (inv-∙ (((a ∙ b) ∙ c)) d
    ∙ ap (d ⁻¹ ∙_) (inv-∙ ((a ∙ b)) c
    ∙ ap (c ⁻¹ ∙_) (inv-∙ a b))))

  -- push a tail y into a 6-fold right-nested chain
  push6 : {r s t u v w z : A}
          (a : r ≡ s) (b : s ≡ t) (c : t ≡ u) (d : u ≡ v) (e : v ≡ w) (f : w ≡ z)
          {z' : A} (y : z ≡ z')
        → (a ∙ (b ∙ (c ∙ (d ∙ (e ∙ f))))) ∙ y
        ≡ a ∙ (b ∙ (c ∙ (d ∙ (e ∙ (f ∙ y)))))
  push6 a b c d e f y =
      ∙-assoc a (b ∙ (c ∙ (d ∙ (e ∙ f)))) y
    ∙ ap (a ∙_) (∙-assoc b (c ∙ (d ∙ (e ∙ f))) y
    ∙ ap (b ∙_) (∙-assoc c (d ∙ (e ∙ f)) y
    ∙ ap (c ∙_) (∙-assoc d (e ∙ f) y
    ∙ ap (d ∙_) (∙-assoc e f y))))

  -- distribute a whiskering `ap φ` over a 7-fold right-nested chain
  apdist7 : {B : Type 𝓥} (φ : A → B) {p0 p1 p2 p3 p4 p5 p6 p7 : A}
            (a : p0 ≡ p1) (b : p1 ≡ p2) (c : p2 ≡ p3) (d : p3 ≡ p4)
            (e : p4 ≡ p5) (f : p5 ≡ p6) (h : p6 ≡ p7)
          → ap φ (a ∙ (b ∙ (c ∙ (d ∙ (e ∙ (f ∙ h))))))
          ≡ ap φ a ∙ (ap φ b ∙ (ap φ c ∙ (ap φ d ∙ (ap φ e ∙ (ap φ f ∙ ap φ h)))))
  apdist7 φ a b c d e f h =
      ap-∙ φ a (b ∙ (c ∙ (d ∙ (e ∙ (f ∙ h)))))
    ∙ ap (ap φ a ∙_) (ap-∙ φ b (c ∙ (d ∙ (e ∙ (f ∙ h))))
    ∙ ap (ap φ b ∙_) (ap-∙ φ c (d ∙ (e ∙ (f ∙ h)))
    ∙ ap (ap φ c ∙_) (ap-∙ φ d (e ∙ (f ∙ h))
    ∙ ap (ap φ d ∙_) (ap-∙ φ e (f ∙ h)
    ∙ ap (ap φ e ∙_) (ap-∙ φ f h)))))

  apdist6 : {B : Type 𝓥} (φ : A → B) {p0 p1 p2 p3 p4 p5 p6 : A}
            (a : p0 ≡ p1) (b : p1 ≡ p2) (c : p2 ≡ p3) (d : p3 ≡ p4)
            (e : p4 ≡ p5) (f : p5 ≡ p6)
          → ap φ (a ∙ (b ∙ (c ∙ (d ∙ (e ∙ f)))))
          ≡ ap φ a ∙ (ap φ b ∙ (ap φ c ∙ (ap φ d ∙ (ap φ e ∙ ap φ f))))
  apdist6 φ a b c d e f =
      ap-∙ φ a (b ∙ (c ∙ (d ∙ (e ∙ f))))
    ∙ ap (ap φ a ∙_) (ap-∙ φ b (c ∙ (d ∙ (e ∙ f)))
    ∙ ap (ap φ b ∙_) (ap-∙ φ c (d ∙ (e ∙ f))
    ∙ ap (ap φ c ∙_) (ap-∙ φ d (e ∙ f)
    ∙ ap (ap φ d ∙_) (ap-∙ φ e f))))

------------------------------------------------------------------------
-- §4e  Projection lemmas for `injr` (Rocq al.v / pp_C.v `ccr_ir_*`).
--      We are free to choose the RHS forms since the factor proofs are
--      explicit equational chains (not ssreflect rewrites).
------------------------------------------------------------------------

-- helpers closing the refl-case cancellations
private
  mid-cancel : {A : Type 𝓤} {x y : A} (a : x ≡ y)
             → refl x ≡ (a ∙ refl y) ∙ a ⁻¹
  mid-cancel a = (right-inv a) ⁻¹ ∙ ap (_∙ a ⁻¹) ((right-unit a) ⁻¹)

  mid-cancel-l : {A : Type 𝓤} {x y : A} (a : x ≡ y)
               → refl y ≡ (a ⁻¹ ∙ refl x) ∙ a
  mid-cancel-l a = (left-inv a) ⁻¹ ∙ ap (_∙ a) ((right-unit (a ⁻¹)) ⁻¹)

  -- the closed zig-zag: block1 ∙ block3 collapses to refl.
  zigzag : {A : Type 𝓤} {A0 A1 A2 A3 : A}
           (t : A1 ≡ A0) (X : A1 ≡ A2) (r : A2 ≡ A3)
         → ((t ⁻¹ ∙ X) ∙ r) ∙ ((r ⁻¹ ∙ X ⁻¹) ∙ t) ≡ refl A0
  zigzag (refl _) (refl _) (refl _) = refl _

-- injr IGNORES a 1st-arg path: endpoints only.
ccr-ir-pme1 : {Cc Dd Q R : Cat} {f f' : Map Cc Dd} (j : Map Q R) (p : f ≡ f')
            → ccr injr (product-map-eq1 j p)
            ≡ injr-product-map f j ∙ (injr-product-map f' j) ⁻¹
ccr-ir-pme1 j (refl _) = (right-inv (injr-product-map _ j)) ⁻¹

-- injr SEES a 2nd-arg path.
ccr-ir-pme2 : {Cc Dd Q R : Cat} (f : Map Cc Dd) {j j' : Map Q R} (H : j ≡ j')
            → ccr injr (product-map-eq2 f H)
            ≡ injr-product-map f j ∙ ccl injr H ∙ (injr-product-map f j') ⁻¹
ccr-ir-pme2 f (refl _) = mid-cancel (injr-product-map f _)

-- injr through a right-whisker (pre-compose by m).
ccr-ir-ccl : {A B P Q : Cat} (m : Map Q P) {a b : Map P (A ×c B)} (X : a ≡ b)
           → ccr injr (ccl m X)
           ≡ (composeA injr a m) ⁻¹ ∙ ccl m (ccr injr X) ∙ composeA injr b m
ccr-ir-ccl m (refl _) = mid-cancel-l (composeA injr _ m)

-- injr through the product associator, via the pentagon.
ccr-ir-composeA : {B C0 C1 C2 D : Cat}
                  (pk : Map C2 (D ×c B)) (pg : Map C1 C2) (ph : Map C0 C1)
                → ccr injr (composeA pk pg ph)
                ≡ (composeA injr (comp pk pg) ph) ⁻¹
                    ∙ (ccl ph (composeA injr pk pg)) ⁻¹
                    ∙ composeA (comp injr pk) pg ph
                    ∙ composeA injr pk (comp pg ph)
ccr-ir-composeA pk pg ph = c≡ ∙ reassoc
  where
  a = ccl ph (composeA injr pk pg)
  b = composeA injr (comp pk pg) ph
  L = composeA (comp injr pk) pg ph
  R = composeA injr pk (comp pg ph)
  c = ccr injr (composeA pk pg ph)
  P : L ∙ R ≡ a ∙ b ∙ c
  P = pentagonator injr pk pg ph
  abc : a ∙ (b ∙ c) ≡ L ∙ R
  abc = (∙-assoc a b c) ⁻¹ ∙ P ⁻¹
  bc : b ∙ c ≡ a ⁻¹ ∙ (L ∙ R)
  bc = (cancL a (b ∙ c)) ⁻¹ ∙ ap (a ⁻¹ ∙_) abc
  c≡ : c ≡ b ⁻¹ ∙ (a ⁻¹ ∙ (L ∙ R))
  c≡ = (cancL b c) ⁻¹ ∙ ap (b ⁻¹ ∙_) bc
  reassoc : b ⁻¹ ∙ (a ⁻¹ ∙ (L ∙ R)) ≡ (b ⁻¹ ∙ a ⁻¹) ∙ L ∙ R
  reassoc =
      ap (b ⁻¹ ∙_) ((∙-assoc (a ⁻¹) L R) ⁻¹)
    ∙ (∙-assoc (b ⁻¹) (a ⁻¹ ∙ L) R) ⁻¹
    ∙ ap (_∙ R) ((∙-assoc (b ⁻¹) (a ⁻¹) L) ⁻¹)

-- injr through `lw (product-map k Id)` (the 𝟏-distributor, general C).
ccr-ir-ccr-pm-C : {P D2 E2 C : Cat} (k : Map E2 D2)
                  {a b : Map P (E2 ×c C)} (Y : a ≡ b)
                → ccr injr (ccr (product-map k (idMap C)) Y)
                ≡ ((composeA injr (product-map k (idMap C)) a ⁻¹
                     ∙ ccl a (injr-product-map k (idMap C)))
                    ∙ composeA (idMap C) injr a)
                  ∙ ccr (idMap C) (ccr injr Y)
                  ∙ ((composeA (idMap C) injr b ⁻¹
                     ∙ (ccl b (injr-product-map k (idMap C))) ⁻¹)
                    ∙ composeA injr (product-map k (idMap C)) b)
ccr-ir-ccr-pm-C {P} {D2} {E2} {C} k {a} (refl _) =
  (ap (_∙ blk3) (right-unit blk1) ∙ zigzag cA1 X cA2) ⁻¹
  where
  cA1 = composeA injr (product-map k (idMap C)) a
  X   = ccl a (injr-product-map k (idMap C))
  cA2 = composeA (idMap C) injr a
  blk1 = (cA1 ⁻¹ ∙ X) ∙ cA2
  blk3 = (cA2 ⁻¹ ∙ X ⁻¹) ∙ cA1

------------------------------------------------------------------------
-- §4f  Projection lemmas for `injl` (Rocq al.v / pp_C.v `ccr_il_*`).
--      Mechanical mirror of §4e (injr → injl, injr-product-map →
--      injl-product-map; note injl SEES the first coordinate so the
--      injl-product-map codomain is `comp f injl`, not `comp Id injl`).
------------------------------------------------------------------------

ccr-il-pme1 : {Cc Dd Q R : Cat} {f f' : Map Cc Dd} (j : Map Q R) (p : f ≡ f')
            → ccr injl (product-map-eq1 j p)
            ≡ injl-product-map f j ∙ ccl injl p ∙ (injl-product-map f' j) ⁻¹
ccr-il-pme1 j (refl _) = mid-cancel (injl-product-map _ j)

ccr-il-pme2 : {Cc Dd Q R : Cat} (f : Map Cc Dd) {j j' : Map Q R} (H : j ≡ j')
            → ccr injl (product-map-eq2 f H)
            ≡ injl-product-map f j ∙ (injl-product-map f j') ⁻¹
ccr-il-pme2 f (refl _) = (right-inv (injl-product-map f _)) ⁻¹

ccr-il-ccl : {A B P Q : Cat} (m : Map Q P) {a b : Map P (A ×c B)} (X : a ≡ b)
           → ccr injl (ccl m X)
           ≡ (composeA injl a m) ⁻¹ ∙ ccl m (ccr injl X) ∙ composeA injl b m
ccr-il-ccl m (refl _) = mid-cancel-l (composeA injl _ m)

ccr-il-composeA : {B C0 C1 C2 D : Cat}
                  (pk : Map C2 (D ×c B)) (pg : Map C1 C2) (ph : Map C0 C1)
                → ccr injl (composeA pk pg ph)
                ≡ (composeA injl (comp pk pg) ph) ⁻¹
                    ∙ (ccl ph (composeA injl pk pg)) ⁻¹
                    ∙ composeA (comp injl pk) pg ph
                    ∙ composeA injl pk (comp pg ph)
ccr-il-composeA pk pg ph = c≡ ∙ reassoc
  where
  a = ccl ph (composeA injl pk pg)
  b = composeA injl (comp pk pg) ph
  L = composeA (comp injl pk) pg ph
  R = composeA injl pk (comp pg ph)
  c = ccr injl (composeA pk pg ph)
  P : L ∙ R ≡ a ∙ b ∙ c
  P = pentagonator injl pk pg ph
  abc : a ∙ (b ∙ c) ≡ L ∙ R
  abc = (∙-assoc a b c) ⁻¹ ∙ P ⁻¹
  bc : b ∙ c ≡ a ⁻¹ ∙ (L ∙ R)
  bc = (cancL a (b ∙ c)) ⁻¹ ∙ ap (a ⁻¹ ∙_) abc
  c≡ : c ≡ b ⁻¹ ∙ (a ⁻¹ ∙ (L ∙ R))
  c≡ = (cancL b c) ⁻¹ ∙ ap (b ⁻¹ ∙_) bc
  reassoc : b ⁻¹ ∙ (a ⁻¹ ∙ (L ∙ R)) ≡ (b ⁻¹ ∙ a ⁻¹) ∙ L ∙ R
  reassoc =
      ap (b ⁻¹ ∙_) ((∙-assoc (a ⁻¹) L R) ⁻¹)
    ∙ (∙-assoc (b ⁻¹) (a ⁻¹ ∙ L) R) ⁻¹
    ∙ ap (_∙ R) ((∙-assoc (b ⁻¹) (a ⁻¹) L) ⁻¹)

ccr-il-ccr-pm-C : {P D2 E2 C : Cat} (k : Map E2 D2)
                  {a b : Map P (E2 ×c C)} (Y : a ≡ b)
                → ccr injl (ccr (product-map k (idMap C)) Y)
                ≡ ((composeA injl (product-map k (idMap C)) a ⁻¹
                     ∙ ccl a (injl-product-map k (idMap C)))
                    ∙ composeA k injl a)
                  ∙ ccr k (ccr injl Y)
                  ∙ ((composeA k injl b ⁻¹
                     ∙ (ccl b (injl-product-map k (idMap C))) ⁻¹)
                    ∙ composeA injl (product-map k (idMap C)) b)
ccr-il-ccr-pm-C {P} {D2} {E2} {C} k {a} (refl _) =
  (ap (_∙ blk3) (right-unit blk1) ∙ zigzag cA1 X cA2) ⁻¹
  where
  cA1 = composeA injl (product-map k (idMap C)) a
  X   = ccl a (injl-product-map k (idMap C))
  cA2 = composeA k injl a
  blk1 = (cA1 ⁻¹ ∙ X) ∙ cA2
  blk3 = (cA2 ⁻¹ ∙ X ⁻¹) ∙ cA1

------------------------------------------------------------------------
-- §5  The product-pentagon RHS, as a pasting diagram (Rocq
--     dsl_C.`prodpent_rhs_C`).
------------------------------------------------------------------------

prodpent-rhs-C : {C0 C1 C2 D C : Cat}
                 (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1)
               → product-map (comp (comp k g) h) (idMap C)
               ≡ product-map (comp k (comp g h)) (idMap C)
prodpent-rhs-C {C0} {C1} {C2} {D} {C} k g h =
    product-map-eq2 (comp (comp k g) h) (sy (ul Ic))
  ⊙ pmc h (comp k g) Ic Ic
  ⊙ rw (product-map h Ic) (product-map-eq2 (comp k g) (sy (ul Ic)) ⊙ pmc g k Ic Ic)
  ⊙ al (product-map k Ic) (product-map g Ic) (product-map h Ic)
  ⊙ lw (product-map k Ic) (sy (pmc h g Ic Ic) ⊙ product-map-eq2 (comp g h) (ul Ic))
  ⊙ sy (pmc (comp g h) k Ic Ic)
  ⊙ sy (product-map-eq2 (comp k (comp g h)) (sy (ul Ic)))
  where Ic = idMap C

------------------------------------------------------------------------
-- §6  The two factor proofs.
------------------------------------------------------------------------

-- The seven cells of prodpent-rhs-C, named so the projection distributes.
module Cells {C0 C1 C2 D C : Cat}
             (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1) where
  Ic = idMap C
  pk = product-map k Ic
  pg = product-map g Ic
  ph = product-map h Ic
  cp1 = product-map-eq2 (comp (comp k g) h) (sy (ul Ic))
  cp2 = pmc h (comp k g) Ic Ic
  cp3 = rw ph (product-map-eq2 (comp k g) (sy (ul Ic)) ⊙ pmc g k Ic Ic)
  cp4 = al pk pg ph
  cp5 = lw pk (sy (pmc h g Ic Ic) ⊙ product-map-eq2 (comp g h) (ul Ic))
  cp6 = sy (pmc (comp g h) k Ic Ic)
  cp7 = sy (product-map-eq2 (comp k (comp g h)) (sy (ul Ic)))

  rhs-is : prodpent-rhs-C k g h ≡ cp1 ⊙ cp2 ⊙ cp3 ⊙ cp4 ⊙ cp5 ⊙ cp6 ⊙ cp7
  rhs-is = refl _

-- Distribute a whisker W over the 7-fold composite.
module Distribute {C0 C1 C2 D C E : Cat}
                  (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1)
                  (w : Map (D ×c C) E) where
  open Cells {C = C} k g h
  W : Map (C0 ×c C) (D ×c C) → Map (C0 ×c C) E
  W u = comp w u
  dist : ccr w (prodpent-rhs-C k g h)
       ≡ ccr w cp1 ∙ (ccr w cp2 ∙ (ccr w cp3 ∙ (ccr w cp4
           ∙ (ccr w cp5 ∙ (ccr w cp6 ∙ ccr w cp7)))))
  dist =
      ap-∙ W cp1 (cp2 ⊙ cp3 ⊙ cp4 ⊙ cp5 ⊙ cp6 ⊙ cp7)
    ∙ ap (ccr w cp1 ∙_)
        ( ap-∙ W cp2 (cp3 ⊙ cp4 ⊙ cp5 ⊙ cp6 ⊙ cp7)
        ∙ ap (ccr w cp2 ∙_)
            ( ap-∙ W cp3 (cp4 ⊙ cp5 ⊙ cp6 ⊙ cp7)
            ∙ ap (ccr w cp3 ∙_)
                ( ap-∙ W cp4 (cp5 ⊙ cp6 ⊙ cp7)
                ∙ ap (ccr w cp4 ∙_)
                    ( ap-∙ W cp5 (cp6 ⊙ cp7)
                    ∙ ap (ccr w cp5 ∙_) (ap-∙ W cp6 cp7)))))

-- The injr factor (second coordinate all-Id ⇒ a unit loop).
module InjrFactor {C0 C1 C2 D C : Cat}
                  (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1) where
  open Cells {C = C} k g h
  irkgh  = injr-product-map (comp (comp k g) h) Ic
  irkgh' = injr-product-map (comp k (comp g h)) Ic

  lhs : ccr injr (product-map-eq1 Ic (composeA k g h)) ≡ irkgh ∙ irkgh' ⁻¹
  lhs = ccr-ir-pme1 Ic (composeA k g h)

  -- the whisker distribution at w = injr
  rhs-dist : ccr injr (prodpent-rhs-C k g h)
           ≡ ccr injr cp1 ∙ (ccr injr cp2 ∙ (ccr injr cp3 ∙ (ccr injr cp4
               ∙ (ccr injr cp5 ∙ (ccr injr cp6 ∙ ccr injr cp7)))))
  rhs-dist = Distribute.dist k g h injr

  -- inner sub-composites of the two whiskered faces
  X3 = product-map-eq2 (comp k g) (sy (ul Ic)) ⊙ pmc g k Ic Ic
  X5 = sy (pmc h g Ic Ic) ⊙ product-map-eq2 (comp g h) (ul Ic)

  pkg = product-map (comp k g) Ic
  pgh = product-map (comp g h) Ic
  irk = injr-product-map k Ic

  -- the seven face projections (each = one §4e lemma; RHS spelled out)
  prj1 : ccr injr cp1
       ≡ injr-product-map (comp (comp k g) h) Ic ∙ ccl injr (sy (ul Ic))
           ∙ (injr-product-map (comp (comp k g) h) (comp Ic Ic)) ⁻¹
  prj1 = ccr-ir-pme2 (comp (comp k g) h) (sy (ul Ic))

  prj2 : ccr injr cp2 ≡ pmc-legr h (comp k g) Ic Ic
  prj2 = pmc-injr h (comp k g) Ic Ic

  prj3 : ccr injr cp3
       ≡ (composeA injr pkg ph) ⁻¹ ∙ ccl ph (ccr injr X3) ∙ composeA injr (comp pk pg) ph
  prj3 = ccr-ir-ccl ph X3

  prj4 : ccr injr cp4
       ≡ (composeA injr (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injr pk pg)) ⁻¹
           ∙ composeA (comp injr pk) pg ph ∙ composeA injr pk (comp pg ph)
  prj4 = ccr-ir-composeA pk pg ph

  prj5 : ccr injr cp5
       ≡ ((composeA injr pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) irk)
            ∙ composeA Ic injr (comp pg ph))
         ∙ ccr Ic (ccr injr X5)
         ∙ ((composeA Ic injr pgh ⁻¹ ∙ (ccl pgh irk) ⁻¹) ∙ composeA injr pk pgh)
  prj5 = ccr-ir-ccr-pm-C k X5

  prj6 : ccr injr cp6 ≡ (pmc-legr (comp g h) k Ic Ic) ⁻¹
  prj6 = ap-⁻¹ (comp injr) (pmc (comp g h) k Ic Ic)
       ∙ ap _⁻¹ (pmc-injr (comp g h) k Ic Ic)

  prj7 : ccr injr cp7
       ≡ (injr-product-map (comp k (comp g h)) Ic ∙ ccl injr (sy (ul Ic))
           ∙ (injr-product-map (comp k (comp g h)) (comp Ic Ic)) ⁻¹) ⁻¹
  prj7 = ap-⁻¹ (comp injr) (product-map-eq2 (comp k (comp g h)) (sy (ul Ic)))
       ∙ ap _⁻¹ (ccr-ir-pme2 (comp k (comp g h)) (sy (ul Ic)))

  projected =
    ∙-cong prj1 (∙-cong prj2 (∙-cong prj3 (∙-cong prj4
      (∙-cong prj5 (∙-cong prj6 prj7)))))

  -- The fully projected telescope (= `projected`'s RHS), spelled out.
  Tel : comp injr (product-map (comp (comp k g) h) Ic)
      ≡ comp injr (product-map (comp k (comp g h)) Ic)
  Tel =
      (injr-product-map (comp (comp k g) h) Ic ∙ ccl injr (sy (ul Ic))
        ∙ (injr-product-map (comp (comp k g) h) (comp Ic Ic)) ⁻¹)
    ∙ (pmc-legr h (comp k g) Ic Ic
    ∙ (((composeA injr pkg ph) ⁻¹ ∙ ccl ph (ccr injr X3) ∙ composeA injr (comp pk pg) ph)
    ∙ (((composeA injr (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injr pk pg)) ⁻¹
          ∙ composeA (comp injr pk) pg ph ∙ composeA injr pk (comp pg ph))
    ∙ ((((composeA injr pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) irk)
            ∙ composeA Ic injr (comp pg ph))
          ∙ ccr Ic (ccr injr X5)
          ∙ ((composeA Ic injr pgh ⁻¹ ∙ (ccl pgh irk) ⁻¹) ∙ composeA injr pk pgh))
    ∙ ((pmc-legr (comp g h) k Ic Ic) ⁻¹
    ∙ ((injr-product-map (comp k (comp g h)) Ic ∙ ccl injr (sy (ul Ic))
          ∙ (injr-product-map (comp k (comp g h)) (comp Ic Ic)) ⁻¹) ⁻¹))))))

  -- inner expansions of the two folded sub-projections (ccr injr X3/X5).
  -- Each is `ap-∙` (split the ⊙) then ccr-ir-pme2 + pmc-injr on the pieces.
  qX3 : ccr injr X3
      ≡ (injr-product-map (comp k g) Ic ∙ ccl injr (sy (ul Ic))
          ∙ (injr-product-map (comp k g) (comp Ic Ic)) ⁻¹)
        ∙ pmc-legr g k Ic Ic
  qX3 = ap-∙ (comp injr) (product-map-eq2 (comp k g) (sy (ul Ic))) (pmc g k Ic Ic)
      ∙ ∙-cong (ccr-ir-pme2 (comp k g) (sy (ul Ic))) (pmc-injr g k Ic Ic)

  -- ccr injr X3 with its internal Jrkg-pair cancelled (solveR flatten + cancL).
  -- Demonstrates the Cayley solver + cancL on a real M sub-goal.
  qX3c : ccr injr X3
       ≡ injr-product-map (comp k g) Ic
         ∙ (ccl injr (sy (ul Ic))
         ∙ (composeA Ic Ic injr
         ∙ (ccr Ic (injr-product-map g Ic ⁻¹)
         ∙ ((composeA Ic injr (product-map g Ic)) ⁻¹
         ∙ (ccl (product-map g Ic) (injr-product-map k Ic ⁻¹)
         ∙ composeA injr (product-map k Ic) (product-map g Ic))))))
  qX3c = qX3
       ∙ solveR
           ((( ι ir ⊕ ι uu) ⊕ ι (jr ⁻¹))
             ⊕ (((((ι jr ⊕ ι a1) ⊕ ι c3) ⊕ ι (a4 ⁻¹)) ⊕ ι c5) ⊕ ι a6))
           ( ι ir ⊕ (ι uu ⊕ (ι (jr ⁻¹) ⊕ (ι jr ⊕ (ι a1 ⊕ (ι c3
             ⊕ (ι (a4 ⁻¹) ⊕ (ι c5 ⊕ ι a6))))))))
           (refl _)
       ∙ ap (λ z → ir ∙ (uu ∙ z))
            (cancL jr (a1 ∙ (c3 ∙ ((a4 ⁻¹) ∙ (c5 ∙ a6)))))
    where
    ir = injr-product-map (comp k g) Ic
    uu = ccl injr (sy (ul Ic))
    jr = injr-product-map (comp k g) (comp Ic Ic)
    a1 = composeA Ic Ic injr
    c3 = ccr Ic (injr-product-map g Ic ⁻¹)
    a4 = composeA Ic injr (product-map g Ic)
    c5 = ccl (product-map g Ic) (injr-product-map k Ic ⁻¹)
    a6 = composeA injr (product-map k Ic) (product-map g Ic)

  qX5 : ccr injr X5
      ≡ (pmc-legr h g Ic Ic) ⁻¹
        ∙ (injr-product-map (comp g h) (comp Ic Ic) ∙ ccl injr (ul Ic)
            ∙ (injr-product-map (comp g h) Ic) ⁻¹)
  qX5 = ap-∙ (comp injr) (sy (pmc h g Ic Ic)) (product-map-eq2 (comp g h) (ul Ic))
      ∙ ∙-cong (ap-⁻¹ (comp injr) (pmc h g Ic Ic) ∙ ap _⁻¹ (pmc-injr h g Ic Ic))
               (ccr-ir-pme2 (comp g h) (ul Ic))

  -- ccr injr X5 with its internal Jgh-pair cancelled (invflat6 + solveR + cancL).
  qX5c : ccr injr X5
       ≡ (composeA injr (product-map g Ic) (product-map h Ic)) ⁻¹
         ∙ ((ccl (product-map h Ic) (injr-product-map g Ic ⁻¹)) ⁻¹
         ∙ (((composeA Ic injr (product-map h Ic)) ⁻¹) ⁻¹
         ∙ ((ccr Ic (injr-product-map h Ic ⁻¹)) ⁻¹
         ∙ ((composeA Ic Ic injr) ⁻¹
         ∙ (ccl injr (ul Ic)
         ∙ (injr-product-map (comp g h) Ic) ⁻¹)))))
  qX5c = qX5
       ∙ ap (_∙ ((jgh ∙ uu5) ∙ (irgh ⁻¹))) (invflat6 jgh b1 b2 b3 b4 b5)
       ∙ solveR
           ((ι (b5 ⁻¹) ⊕ (ι (b4 ⁻¹) ⊕ (ι (b3 ⁻¹) ⊕ (ι (b2 ⁻¹) ⊕ (ι (b1 ⁻¹) ⊕ ι (jgh ⁻¹))))))
             ⊕ ((ι jgh ⊕ ι uu5) ⊕ ι (irgh ⁻¹)))
           (ι (b5 ⁻¹) ⊕ (ι (b4 ⁻¹) ⊕ (ι (b3 ⁻¹) ⊕ (ι (b2 ⁻¹) ⊕ (ι (b1 ⁻¹)
             ⊕ (ι (jgh ⁻¹) ⊕ (ι jgh ⊕ (ι uu5 ⊕ ι (irgh ⁻¹)))))))))
           (refl _)
       ∙ ap (λ z → (b5 ⁻¹) ∙ ((b4 ⁻¹) ∙ ((b3 ⁻¹) ∙ ((b2 ⁻¹) ∙ ((b1 ⁻¹) ∙ z)))))
            (cancL jgh (uu5 ∙ (irgh ⁻¹)))
    where
    jgh  = injr-product-map (comp g h) (comp Ic Ic)
    uu5  = ccl injr (ul Ic)
    irgh = injr-product-map (comp g h) Ic
    b1 = composeA Ic Ic injr
    b2 = ccr Ic (injr-product-map h Ic ⁻¹)
    b3 = (composeA Ic injr (product-map h Ic)) ⁻¹
    b4 = ccl (product-map h Ic) (injr-product-map g Ic ⁻¹)
    b5 = composeA injr (product-map g Ic) (product-map h Ic)

  -- m6 / m11 fully expanded: inner IR-pair cancelled (qX3c/qX5c) AND the
  -- outer whiskering ccl ph / ccr Ic distributed (apdist7).
  m6f : ccl ph (ccr injr X3)
      ≡ ccl ph (injr-product-map (comp k g) Ic)
        ∙ (ccl ph (ccl injr (sy (ul Ic)))
        ∙ (ccl ph (composeA Ic Ic injr)
        ∙ (ccl ph (ccr Ic (injr-product-map g Ic ⁻¹))
        ∙ (ccl ph ((composeA Ic injr (product-map g Ic)) ⁻¹)
        ∙ (ccl ph (ccl (product-map g Ic) (injr-product-map k Ic ⁻¹))
        ∙ ccl ph (composeA injr (product-map k Ic) (product-map g Ic)))))))
  m6f = ap (ccl ph) qX3c
      ∙ apdist7 (λ m → comp m ph)
          (injr-product-map (comp k g) Ic)
          (ccl injr (sy (ul Ic)))
          (composeA Ic Ic injr)
          (ccr Ic (injr-product-map g Ic ⁻¹))
          ((composeA Ic injr (product-map g Ic)) ⁻¹)
          (ccl (product-map g Ic) (injr-product-map k Ic ⁻¹))
          (composeA injr (product-map k Ic) (product-map g Ic))

  m11f : ccr Ic (ccr injr X5)
       ≡ ccr Ic ((composeA injr (product-map g Ic) (product-map h Ic)) ⁻¹)
         ∙ (ccr Ic ((ccl (product-map h Ic) (injr-product-map g Ic ⁻¹)) ⁻¹)
         ∙ (ccr Ic (((composeA Ic injr (product-map h Ic)) ⁻¹) ⁻¹)
         ∙ (ccr Ic ((ccr Ic (injr-product-map h Ic ⁻¹)) ⁻¹)
         ∙ (ccr Ic ((composeA Ic Ic injr) ⁻¹)
         ∙ (ccr Ic (ccl injr (ul Ic))
         ∙ ccr Ic ((injr-product-map (comp g h) Ic) ⁻¹))))))
  m11f = ap (ccr Ic) qX5c
       ∙ apdist7 (comp Ic)
           ((composeA injr (product-map g Ic) (product-map h Ic)) ⁻¹)
           ((ccl (product-map h Ic) (injr-product-map g Ic ⁻¹)) ⁻¹)
           (((composeA Ic injr (product-map h Ic)) ⁻¹) ⁻¹)
           ((ccr Ic (injr-product-map h Ic ⁻¹)) ⁻¹)
           ((composeA Ic Ic injr) ⁻¹)
           (ccl injr (ul Ic))
           ((injr-product-map (comp g h) Ic) ⁻¹)

  -- atom abbreviations for the collapse chain
  u    = ccl (injr {C0} {C}) (sy (ul Ic))
  jr1  = injr-product-map (comp (comp k g) h) (comp Ic Ic)   -- JR_{kgh}
  jr2  = injr-product-map (comp k (comp g h)) (comp Ic Ic)   -- JR_{kgh'}
  irh  = injr-product-map h Ic
  irg  = injr-product-map g Ic
  irgh = injr-product-map (comp g h) Ic
  irkg = injr-product-map (comp k g) Ic

  -- M : the conjugation middle (a loop comp Ic injr ≡ comp Ic injr).
  -- After the free cancellations Tel = irkgh ∙ (M ∙ irkgh' ⁻¹); the genuine
  -- pentagon/unit content is exactly  M ≡ refl.
  M : comp Ic (injr {C0} {C}) ≡ comp Ic (injr {C0} {C})
  M = u
    ∙ (composeA Ic Ic (injr {C0} {C})
    ∙ (ccr Ic (irh ⁻¹)
    ∙ ((composeA Ic injr ph) ⁻¹
    ∙ (ccl ph (irkg ⁻¹)
    ∙ (ccl ph (ccr injr X3)
    ∙ ((ccl ph (composeA injr pk pg)) ⁻¹
    ∙ (composeA (comp injr pk) pg ph
    ∙ (ccl (comp pg ph) irk
    ∙ (composeA Ic injr (comp pg ph)
    ∙ (ccr Ic (ccr injr X5)
    ∙ ((ccr Ic (irgh ⁻¹)) ⁻¹
    ∙ ((composeA Ic Ic (injr {C0} {C})) ⁻¹
    ∙ u ⁻¹))))))))))))

  -- the seven blocks of Tel, named (must decompose Tel definitionally).
  b1 = (irkgh ∙ u) ∙ jr1 ⁻¹
  b2 = pmc-legr h (comp k g) Ic Ic
  b3 = ((composeA injr pkg ph) ⁻¹ ∙ ccl ph (ccr injr X3)) ∙ composeA injr (comp pk pg) ph
  b4 = (((composeA injr (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injr pk pg)) ⁻¹)
          ∙ composeA (comp injr pk) pg ph) ∙ composeA injr pk (comp pg ph)
  b5 = (((composeA injr pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) irk)
            ∙ composeA Ic injr (comp pg ph)) ∙ ccr Ic (ccr injr X5))
        ∙ ((composeA Ic injr pgh ⁻¹ ∙ (ccl pgh irk) ⁻¹) ∙ composeA injr pk pgh)
  b6 = (pmc-legr (comp g h) k Ic Ic) ⁻¹
  b7 = (irkgh' ∙ u ∙ jr2 ⁻¹) ⁻¹

  tel-decomp : Tel ≡ b1 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (b5 ∙ (b6 ∙ b7)))))
  tel-decomp = refl _

  -- survivor atoms (the 13 interior cells of M, after u)
  m2  = composeA Ic Ic (injr {C0} {C})
  m3  = ccr Ic (irh ⁻¹)
  m4  = (composeA Ic injr ph) ⁻¹
  m5  = ccl ph (irkg ⁻¹)
  m6  = ccl ph (ccr injr X3)
  m7  = (ccl ph (composeA injr pk pg)) ⁻¹
  m8  = composeA (comp injr pk) pg ph
  m9  = ccl (comp pg ph) irk
  m10 = composeA Ic injr (comp pg ph)
  m11 = ccr Ic (ccr injr X5)
  m12 = (ccr Ic (irgh ⁻¹)) ⁻¹
  m13 = (composeA Ic Ic (injr {C0} {C})) ⁻¹
  -- cancellation pivots
  p9   = composeA injr pkg ph
  p12  = composeA injr (comp pk pg) ph
  p16  = composeA injr pk (comp pg ph)
  p23  = composeA injr pk pgh
  pAp  = composeA Ic injr pgh
  pclk = ccl pgh irk
  e6   = (ccl pgh (irk ⁻¹)) ⁻¹
  d6   = ((composeA Ic injr pgh) ⁻¹) ⁻¹
  b67  = b6 ∙ b7

  -- M with abbreviations (sanity refl-check against the inline M)
  M-check : M ≡ u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10
              ∙ (m11 ∙ (m12 ∙ (m13 ∙ u ⁻¹))))))))))))
  M-check = refl _

  Mflat : comp injr (product-map (comp (comp k g) h) Ic) ≡ comp injr (product-map (comp k (comp g h)) Ic)
  Mflat = irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10
            ∙ (m11 ∙ (m12 ∙ (m13 ∙ (u ⁻¹ ∙ irkgh' ⁻¹))))))))))))))

  -- flatten block 5 (the one with the inner G group), keeping b67 as tail
  flatb5 : b5 ∙ b67 ≡ p16 ⁻¹ ∙ (m9 ∙ (m10 ∙ (m11 ∙ (pAp ⁻¹ ∙ (pclk ⁻¹ ∙ (p23 ∙ b67))))))
  flatb5 =
      ∙-assoc (((p16 ⁻¹ ∙ m9) ∙ m10) ∙ m11) ((pAp ⁻¹ ∙ pclk ⁻¹) ∙ p23) b67
    ∙ ap ((((p16 ⁻¹ ∙ m9) ∙ m10) ∙ m11) ∙_) (fa4 (pAp ⁻¹) (pclk ⁻¹) p23 b67)
    ∙ fa5 (p16 ⁻¹) m9 m10 m11 (pAp ⁻¹ ∙ (pclk ⁻¹ ∙ (p23 ∙ b67)))

  -- flatten b7
  b7flat : b7 ≡ jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹)
  b7flat = inv-∙ (irkgh' ∙ u) (jr2 ⁻¹) ∙ ∙-cong (inv-inv jr2) (inv-∙ irkgh' u)

  -- flatten block 6 ∙ block 7
  flatb67 : b67 ≡ p23 ⁻¹ ∙ (e6 ∙ (d6 ∙ (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹)))))))
  flatb67 =
      ap (_∙ b7) (invflat6 jr2 m2 (ccr Ic (irgh ⁻¹)) ((composeA Ic injr pgh) ⁻¹) (ccl pgh (irk ⁻¹)) p23)
    ∙ push6 (p23 ⁻¹) e6 d6 m12 m13 (jr2 ⁻¹) b7
    ∙ ap (λ z → p23 ⁻¹ ∙ (e6 ∙ (d6 ∙ (m12 ∙ (m13 ∙ z))))) (ap (jr2 ⁻¹ ∙_) b7flat)

  -- the two involution rewrites used in the telescope cancellations
  e6-pclk : e6 ≡ pclk
  e6-pclk = ap _⁻¹ (ap-⁻¹ (λ m → comp m pgh) irk) ∙ inv-inv pclk

  d6-pAp : d6 ≡ pAp
  d6-pAp = inv-inv pAp

  -- regroup the flat Mflat tail back into M ∙ irkgh' ⁻¹
  mregroup : M ∙ irkgh' ⁻¹ ≡ u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10
              ∙ (m11 ∙ (m12 ∙ (m13 ∙ (u ⁻¹ ∙ irkgh' ⁻¹)))))))))))))
  mregroup =
      ap (_∙ irkgh' ⁻¹) M-check
    ∙ ∙-assoc u _ (irkgh' ⁻¹)
    ∙ ap (u ∙_) (∙-assoc m2 _ (irkgh' ⁻¹)
    ∙ ap (m2 ∙_) (∙-assoc m3 _ (irkgh' ⁻¹)
    ∙ ap (m3 ∙_) (∙-assoc m4 _ (irkgh' ⁻¹)
    ∙ ap (m4 ∙_) (∙-assoc m5 _ (irkgh' ⁻¹)
    ∙ ap (m5 ∙_) (∙-assoc m6 _ (irkgh' ⁻¹)
    ∙ ap (m6 ∙_) (∙-assoc m7 _ (irkgh' ⁻¹)
    ∙ ap (m7 ∙_) (∙-assoc m8 _ (irkgh' ⁻¹)
    ∙ ap (m8 ∙_) (∙-assoc m9 _ (irkgh' ⁻¹)
    ∙ ap (m9 ∙_) (∙-assoc m10 _ (irkgh' ⁻¹)
    ∙ ap (m10 ∙_) (∙-assoc m11 _ (irkgh' ⁻¹)
    ∙ ap (m11 ∙_) (∙-assoc m12 _ (irkgh' ⁻¹)
    ∙ ap (m12 ∙_) (∙-assoc m13 (u ⁻¹) (irkgh' ⁻¹)))))))))))))

  -- ====================================================================
  -- Reduce M to the genuine pentagon/unit core GC, by substituting m6f/m11f
  -- and cancelling the three free IR-pairs (m5·n1, n7·m7, q7·m12).
  -- ====================================================================

  -- sub-atoms of m6 (= m6f's RHS, right-nested as n1 ∙ (n2 ∙ … ∙ n7))
  n1 = ccl ph irkg
  n2 = ccl ph (ccl injr (sy (ul Ic)))
  n3 = ccl ph (composeA Ic Ic injr)
  n4 = ccl ph (ccr Ic (irg ⁻¹))
  n5 = ccl ph ((composeA Ic injr pg) ⁻¹)
  n6 = ccl ph (ccl pg (irk ⁻¹))
  n7 = ccl ph (composeA injr pk pg)

  -- sub-atoms of m11 (= m11f's RHS, right-nested as q1 ∙ (q2 ∙ … ∙ q7))
  q1 = ccr Ic ((composeA injr pg ph) ⁻¹)
  q2 = ccr Ic ((ccl ph (irg ⁻¹)) ⁻¹)
  q3 = ccr Ic (((composeA Ic injr ph) ⁻¹) ⁻¹)
  q4 = ccr Ic ((ccr Ic (irh ⁻¹)) ⁻¹)
  q5 = ccr Ic ((composeA Ic Ic (injr {C0} {C})) ⁻¹)
  q6 = ccr Ic (ccl (injr {C0} {C}) (ul Ic))
  q7 = ccr Ic (irgh ⁻¹)

  T13 = m13 ∙ u ⁻¹
  T7  = m8 ∙ (m9 ∙ (m10 ∙ (m11 ∙ (m12 ∙ T13))))

  -- local reduction of the m5·m6·m7 region: m5 cancels n1, n7 cancels m7.
  red56 : m5 ∙ (m6 ∙ (m7 ∙ T7)) ≡ n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ T7))))
  red56 =
      ap (λ z → m5 ∙ (z ∙ (m7 ∙ T7))) m6f
    ∙ solveR
        (ι m5 ⊕ (((ι n1 ⊕ (ι n2 ⊕ (ι n3 ⊕ (ι n4 ⊕ (ι n5 ⊕ (ι n6 ⊕ ι n7))))))
           ⊕ (ι m7 ⊕ ι T7))))
        (ι m5 ⊕ (ι n1 ⊕ (ι n2 ⊕ (ι n3 ⊕ (ι n4 ⊕ (ι n5 ⊕ (ι n6 ⊕ (ι n7 ⊕ (ι m7 ⊕ ι T7)))))))))
        (refl _)
    ∙ ap (_∙ (n1 ∙ REST)) (ap-⁻¹ (λ m → comp m ph) irkg)
    ∙ cancL n1 REST
    ∙ ap (λ z → n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ z))))) (cancR n7 T7)
    where
    REST = n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ (n7 ∙ (m7 ∙ T7))))))

  -- local reduction of the m11·m12 region: q7 cancels m12.
  red1112 : m11 ∙ (m12 ∙ T13) ≡ q1 ∙ (q2 ∙ (q3 ∙ (q4 ∙ (q5 ∙ (q6 ∙ T13)))))
  red1112 =
      ap (λ z → z ∙ (m12 ∙ T13)) m11f
    ∙ solveR
        (( ι q1 ⊕ (ι q2 ⊕ (ι q3 ⊕ (ι q4 ⊕ (ι q5 ⊕ (ι q6 ⊕ ι q7))))))
          ⊕ (ι m12 ⊕ ι T13))
        (ι q1 ⊕ (ι q2 ⊕ (ι q3 ⊕ (ι q4 ⊕ (ι q5 ⊕ (ι q6 ⊕ (ι q7 ⊕ (ι m12 ⊕ ι T13))))))))
        (refl _)
    ∙ ap (λ z → q1 ∙ (q2 ∙ (q3 ∙ (q4 ∙ (q5 ∙ (q6 ∙ z)))))) (cancR q7 T13)

  -- the genuine pentagon/unit core (Rocq pp_C.v S2–S8): M with the free
  -- IR-pairs cancelled.  All that remains is the unit-loop coherence.
  GC : comp Ic (injr {C0} {C}) ≡ comp Ic (injr {C0} {C})
  GC = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ (m8 ∙ (m9 ∙ (m10
         ∙ (q1 ∙ (q2 ∙ (q3 ∙ (q4 ∙ (q5 ∙ (q6 ∙ (m13 ∙ u ⁻¹))))))))))))))))))

  Mred : M ≡ GC
  Mred =
      ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ z)))) red56
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6
          ∙ (m8 ∙ (m9 ∙ (m10 ∙ z))))))))))))
         red1112

  -- ====================================================================
  -- Collapse GC by the genuine coherence moves (Rocq dsl_C.v injr_factor):
  -- the irk/irg/irh naturality pairs (cn1-n / cn2-collapse / nat3-cps) and
  -- two pentagon legs (pent-expand, forward & reverse), leaving a 12-atom
  -- unit-coherence core GC5 whose tail is `PastingTest.injr-unit-loop`.
  -- ====================================================================

  -- the q-atoms normalised: strip the double inverses left by m11f.
  q1n = (ccr Ic (composeA injr pg ph)) ⁻¹
  q2n = ccr Ic (ccl ph irg)
  q3n = ccr Ic (composeA Ic injr ph)
  q4n = ccr Ic (ccr Ic irh)

  q1≡ : q1 ≡ q1n
  q1≡ = ap-⁻¹ (comp Ic) (composeA injr pg ph)
  q2≡ : q2 ≡ q2n
  q2≡ = ap (ccr Ic) (ap _⁻¹ (ap-⁻¹ (λ m → comp m ph) irg) ∙ inv-inv (ccl ph irg))
  q3≡ : q3 ≡ q3n
  q3≡ = ap (ccr Ic) (inv-inv (composeA Ic injr ph))
  q4≡ : q4 ≡ q4n
  q4≡ = ap (ccr Ic) (ap _⁻¹ (ap-⁻¹ (comp Ic) irh) ∙ inv-inv (ccr Ic irh))

  -- new front atoms produced by the collapse
  cAipg = composeA Ic injr pg
  A∙ = composeA (comp Ic injr) pg ph
  B∙ = composeA Ic (comp injr pg) ph
  D∙ = composeA Ic (comp Ic injr) ph
  E∙ = composeA (comp Ic Ic) injr ph
  Gc = composeA Ic Ic (comp injr ph)
  Hc = ccr (comp Ic Ic) irh
  Kc = composeA Ic Ic (comp Ic (injr {C0} {C}))

  -- the continuations (tails) at each stage
  W56 = q5 ∙ (q6 ∙ (m13 ∙ u ⁻¹))
  RQ  = q2n ∙ (q3n ∙ (q4n ∙ W56))
  RK  = q1n ∙ RQ

  -- GCn : GC with q1..q4 normalised
  GCn = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ (m8 ∙ (m9 ∙ (m10 ∙ RK)))))))))))

  GC≡GCn : GC ≡ GCn
  GC≡GCn =
    ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (n6 ∙ (m8 ∙ (m9 ∙ (m10 ∙ z))))))))))))
       ( ap (λ a → a ∙ (q2 ∙ (q3 ∙ (q4 ∙ W56)))) q1≡
       ∙ ap (λ b → q1n ∙ (b ∙ (q3 ∙ (q4 ∙ W56)))) q2≡
       ∙ ap (λ c → q1n ∙ (q2n ∙ (c ∙ (q4 ∙ W56)))) q3≡
       ∙ ap (λ d → q1n ∙ (q2n ∙ (q3n ∙ (d ∙ W56)))) q4≡ )

  -- (1) irk pair: cn1-n collapses n6 ∙ m8, then n6's inner inverse meets m9.
  red-irk : n6 ∙ (m8 ∙ (m9 ∙ (m10 ∙ RK))) ≡ A∙ ∙ (m10 ∙ RK)
  red-irk =
      cn1-n pg ph (irk ⁻¹) (m9 ∙ (m10 ∙ RK))
    ∙ ap (A∙ ∙_)
        ( ap (_∙ (m9 ∙ (m10 ∙ RK))) (ap-⁻¹ (λ m → comp m (comp pg ph)) irk)
        ∙ cancL m9 (m10 ∙ RK) )

  GC1 = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ (A∙ ∙ (m10 ∙ RK)))))))))

  -- (2) pent leg + cancel n5/q1n
  red-pent : n5 ∙ (A∙ ∙ (m10 ∙ RK)) ≡ B∙ ∙ RQ
  red-pent =
      ap (λ z → z ∙ (A∙ ∙ (m10 ∙ RK))) (ap-⁻¹ (λ m → comp m ph) cAipg)
    ∙ ap ((ccl ph cAipg) ⁻¹ ∙_) (pent-expand Ic injr pg ph RK)
    ∙ ap (λ z → (ccl ph cAipg) ⁻¹ ∙ (ccl ph cAipg ∙ (B∙ ∙ z)))
         (cancR (ccr Ic (composeA injr pg ph)) RQ)
    ∙ cancL (ccl ph cAipg) (B∙ ∙ RQ)

  GC2 = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (B∙ ∙ RQ)))))))

  -- (3) irg pair: cn2-collapse
  red-irg : n4 ∙ (B∙ ∙ (q2n ∙ (q3n ∙ (q4n ∙ W56)))) ≡ D∙ ∙ (q3n ∙ (q4n ∙ W56))
  red-irg = cn2-collapse Ic ph irg (q3n ∙ (q4n ∙ W56))

  GC3 = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (D∙ ∙ (q3n ∙ (q4n ∙ W56))))))))

  -- (4) pentagon leg in reverse
  red-pentrev : n3 ∙ (D∙ ∙ (q3n ∙ (q4n ∙ W56))) ≡ E∙ ∙ (Gc ∙ (q4n ∙ W56))
  red-pentrev = (pent-expand Ic Ic injr ph (q4n ∙ W56)) ⁻¹

  GC4 = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (E∙ ∙ (Gc ∙ (q4n ∙ W56)))))))

  -- (5) irh pair: nat3-cps
  red-nat3 : Gc ∙ (q4n ∙ W56) ≡ Hc ∙ (Kc ∙ W56)
  red-nat3 = nat3-cps Ic Ic irh W56

  GC5 = u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (E∙ ∙ (Hc ∙ (Kc ∙ W56)))))))

  gc-to-gc5 : GC ≡ GC5
  gc-to-gc5 =
      GC≡GCn
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ (n5 ∙ z)))))))) red-irk
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ (n4 ∙ z))))))) red-pent
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (n3 ∙ z)))))) red-irg
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ z))))) red-pentrev
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (E∙ ∙ z)))))) red-nat3

  -- ====================================================================
  -- GC5 → refl : the unit-coherence endgame (Rocq dsl_C.v injr_factor end).
  --   Hp1 expands the associator E∙ (compose-naturality1 / nat1),
  --   HX5 expands the whiskered irh Hc (interchange / xch),
  --   the irh pair and the unitor pairs cancel, leaving exactly the
  --   PastingTest.injr-unit-loop, conjugated by u ∙ m2 / m2⁻¹ ∙ u⁻¹.
  -- ====================================================================

  P∙   = ccl ph (ccl (injr {C1} {C}) (ul Ic))
  Q∙   = ccl (comp (injr {C1} {C}) ph) (ul Ic)
  R∙   = ccl (comp Ic (injr {C0} {C})) (ul Ic)
  cA   = composeA Ic (injr {C1} {C}) ph
  irhc = ccr Ic irh
  q5'  = (ccr Ic m2) ⁻¹

  -- the associator E∙ rewritten by unitor-naturality (compose-naturality1)
  Hp1 : E∙ ≡ P∙ ∙ (cA ∙ Q∙ ⁻¹)
  Hp1 =
      (right-unit E∙) ⁻¹
    ∙ ap (E∙ ∙_) ((right-inv Q∙) ⁻¹)
    ∙ (∙-assoc E∙ Q∙ (Q∙ ⁻¹)) ⁻¹
    ∙ ap (_∙ Q∙ ⁻¹) (compose-naturality1 (injr {C1} {C}) ph (ul Ic))
    ∙ ∙-assoc P∙ cA (Q∙ ⁻¹)

  -- the whiskered irh Hc rewritten by interchange (xch)
  HX5 : Hc ≡ Q∙ ∙ (irhc ∙ R∙ ⁻¹)
  HX5 =
      (right-unit Hc) ⁻¹
    ∙ ap (Hc ∙_) ((right-inv R∙) ⁻¹)
    ∙ (∙-assoc Hc R∙ (R∙ ⁻¹)) ⁻¹
    ∙ ap (_∙ R∙ ⁻¹) (PastingDSL.xch (ul Ic) irh)
    ∙ ∙-assoc Q∙ irhc (R∙ ⁻¹)

  -- n2 is the inverse of the unitor cell P∙ produced by Hp1
  n2≡P⁻¹ : n2 ≡ P∙ ⁻¹
  n2≡P⁻¹ =
      ap (ccl ph) (ap-⁻¹ (λ m → comp m (injr {C1} {C})) (ul Ic))
    ∙ ap-⁻¹ (λ m → comp m ph) (ccl (injr {C1} {C}) (ul Ic))

  Tend = R∙ ⁻¹ ∙ (Kc ∙ W56)

  -- the four cancellations after Hp1/HX5 are substituted and reassociated
  inner : m3 ∙ (m4 ∙ (n2 ∙ (P∙ ∙ (cA ∙ (Q∙ ⁻¹ ∙ (Q∙ ∙ (irhc ∙ Tend))))))) ≡ Tend
  inner =
      ap (λ z → m3 ∙ (m4 ∙ (n2 ∙ (P∙ ∙ (cA ∙ z))))) (cancL Q∙ (irhc ∙ Tend))
    ∙ ap (λ z → m3 ∙ (m4 ∙ (z ∙ (P∙ ∙ (cA ∙ (irhc ∙ Tend)))))) n2≡P⁻¹
    ∙ ap (λ z → m3 ∙ (m4 ∙ z)) (cancL P∙ (cA ∙ (irhc ∙ Tend)))
    ∙ ap (λ z → m3 ∙ z) (cancL cA (irhc ∙ Tend))
    ∙ ap (λ z → z ∙ (irhc ∙ Tend)) (ap-⁻¹ (comp Ic) irh)
    ∙ cancL irhc Tend

  -- the unit-loop finish: peel the conjugation and apply injr-unit-loop
  final-part : u ∙ (m2 ∙ Tend) ≡ refl (comp Ic (injr {C0} {C}))
  final-part =
      ap (λ z → u ∙ (m2 ∙ (R∙ ⁻¹ ∙ (Kc ∙ (z ∙ (q6 ∙ (m13 ∙ u ⁻¹))))))) q5≡q5'
    ∙ ap (λ z → u ∙ (m2 ∙ z))
         (solveR
           (ι (R∙ ⁻¹) ⊕ (ι Kc ⊕ (ι q5' ⊕ (ι q6 ⊕ (ι m13 ⊕ ι (u ⁻¹))))))
           ((ι (R∙ ⁻¹) ⊕ (ι Kc ⊕ (ι q5' ⊕ ι q6))) ⊕ (ι m13 ⊕ ι (u ⁻¹)))
           (refl _))
    ∙ ap (λ z → u ∙ (m2 ∙ (z ∙ (m13 ∙ u ⁻¹)))) (injr-unit-loop (injr {C0} {C}))
    ∙ ap (u ∙_) (cancR m2 (u ⁻¹))
    ∙ right-inv u
    where
    q5≡q5' : q5 ≡ q5'
    q5≡q5' = ap-⁻¹ (comp Ic) m2

  gc5-work : GC5 ≡ refl (comp Ic (injr {C0} {C}))
  gc5-work =
      ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ (z ∙ (Hc ∙ (Kc ∙ W56)))))))) Hp1
    ∙ ap (λ z → u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (n2 ∙ ((P∙ ∙ (cA ∙ Q∙ ⁻¹)) ∙ (z ∙ (Kc ∙ W56)))))))) HX5
    ∙ solveR
        (ι u ⊕ (ι m2 ⊕ (ι m3 ⊕ (ι m4 ⊕ (ι n2 ⊕ ((ι P∙ ⊕ (ι cA ⊕ ι (Q∙ ⁻¹)))
          ⊕ ((ι Q∙ ⊕ (ι irhc ⊕ ι (R∙ ⁻¹))) ⊕ (ι Kc ⊕ ι W56))))))))
        (ι u ⊕ (ι m2 ⊕ (ι m3 ⊕ (ι m4 ⊕ (ι n2 ⊕ (ι P∙ ⊕ (ι cA ⊕ (ι (Q∙ ⁻¹)
          ⊕ (ι Q∙ ⊕ (ι irhc ⊕ (ι (R∙ ⁻¹) ⊕ (ι Kc ⊕ ι W56))))))))))))
        (refl _)
    ∙ ap (λ z → u ∙ (m2 ∙ z)) inner
    ∙ final-part

  -- genuine injr coherence kernel (pentagon + unit loop).
  -- Building blocks VERIFIED (all via the Cayley solver `solveR`):
  --   * qX3c / qX5c   : ccr injr X3 / X5 with inner IR-pairs cancelled.
  --   * m6f / m11f    : m6 / m11 fully expanded — inner IR-pairs cancelled
  --                     AND outer ccl ph / ccr Ic distributed (apdist7).
  --   * red56 / red1112 / Mred : M reduced to the genuine core GC.
  --   * gc-to-gc5     : GC reduced to the 12-atom unit-coherence core GC5.
  --   * gc5-work      : GC5 collapsed to refl (Hp1/HX5 + injr-unit-loop).
  gc5-collapse : GC5 ≡ refl (comp Ic (injr {C0} {C}))
  gc5-collapse = gc5-work

  M-collapse : M ≡ refl (comp Ic (injr {C0} {C}))
  M-collapse = Mred ∙ (gc-to-gc5 ∙ gc5-collapse)


  -- block tails
  R3 = b3 ∙ (b4 ∙ (b5 ∙ b67))
  R4 = b4 ∙ (b5 ∙ b67)
  R5 = b5 ∙ b67
  T2 = b2 ∙ R3

  -- the free reassociation + cancellation sweep (Tel ≡ irkgh ∙ Mflat-tail).
  tel-free : Tel ≡ Mflat
  tel-free =
      fa4 irkgh u (jr1 ⁻¹) T2
    ∙ ap (λ z → irkgh ∙ (u ∙ (jr1 ⁻¹ ∙ z))) (fa7 jr1 m2 m3 m4 m5 p9 R3)
    ∙ ap (λ z → irkgh ∙ (u ∙ z)) (cancL jr1 (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (p9 ∙ R3))))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (p9 ∙ z))))))) (fa4 (p9 ⁻¹) m6 p12 R4)
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ z)))))) (cancR p9 (m6 ∙ (p12 ∙ R4)))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (p12 ∙ z)))))))) (fa5 (p12 ⁻¹) m7 m8 p16 R5)
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ z))))))) (cancR p12 (m7 ∙ (m8 ∙ (p16 ∙ R5))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (p16 ∙ z)))))))))) flatb5
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ z))))))))) (cancR p16 (m9 ∙ (m10 ∙ (m11 ∙ (pAp ⁻¹ ∙ (pclk ⁻¹ ∙ (p23 ∙ b67)))))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10 ∙ (m11 ∙ (pAp ⁻¹ ∙ (pclk ⁻¹ ∙ z))))))))))))))
          (ap (p23 ∙_) flatb67 ∙ cancR p23 (e6 ∙ (d6 ∙ (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹))))))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10 ∙ (m11 ∙ (pAp ⁻¹ ∙ z)))))))))))))
          (ap (λ w → pclk ⁻¹ ∙ (w ∙ (d6 ∙ (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹)))))))) e6-pclk
           ∙ cancL pclk (d6 ∙ (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹)))))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10 ∙ (m11 ∙ z))))))))))))
          (ap (λ w → pAp ⁻¹ ∙ (w ∙ (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹))))))) d6-pAp
           ∙ cancL pAp (m12 ∙ (m13 ∙ (jr2 ⁻¹ ∙ (jr2 ∙ (u ⁻¹ ∙ irkgh' ⁻¹))))))
    ∙ ap (λ z → irkgh ∙ (u ∙ (m2 ∙ (m3 ∙ (m4 ∙ (m5 ∙ (m6 ∙ (m7 ∙ (m8 ∙ (m9 ∙ (m10 ∙ (m11 ∙ (m12 ∙ (m13 ∙ z))))))))))))))
          (cancL jr2 (u ⁻¹ ∙ irkgh' ⁻¹))

  tel-collapse : Tel ≡ irkgh ∙ irkgh' ⁻¹
  tel-collapse =
      tel-free
    ∙ ap (irkgh ∙_)
        ( (mregroup ⁻¹)
        ∙ ap (_∙ irkgh' ⁻¹) M-collapse )

  collapse : ccr injr (prodpent-rhs-C k g h) ≡ irkgh ∙ irkgh' ⁻¹
  collapse = rhs-dist ∙ projected ∙ tel-collapse

prod-pent-C-injr : {C0 C1 C2 D C : Cat}
                   (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1)
                 → ccr injr (product-map-eq1 (idMap C) (composeA k g h))
                 ≡ ccr injr (prodpent-rhs-C k g h)
prod-pent-C-injr k g h = InjrFactor.lhs k g h ∙ (InjrFactor.collapse k g h) ⁻¹

-- The injl factor (Rocq dsl_C.v `injl_factor_dsl` / pp_C.v `prod_pent_C_injl`).
-- injl SEES the first coordinate, so the LHS carries `ccl injl (composeA k g h)`
-- and the collapse closes by ONE pentagon (not a unit loop).  The projection
-- layer mirrors InjrFactor via the §4f `ccr-il-*` lemmas; the genuine pentagon
-- kernel is `tel-collapse-l`.
module InjlFactor {C0 C1 C2 D C : Cat}
                  (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1) where
  open Cells {C = C} k g h
  ilkgh    = injl-product-map (comp (comp k g) h) Ic
  ilkgh'   = injl-product-map (comp k (comp g h)) Ic
  ilkgh-II  = injl-product-map (comp (comp k g) h) (comp Ic Ic)
  ilkgh'-II = injl-product-map (comp k (comp g h)) (comp Ic Ic)

  X3 = product-map-eq2 (comp k g) (sy (ul Ic)) ⊙ pmc g k Ic Ic
  X5 = sy (pmc h g Ic Ic) ⊙ product-map-eq2 (comp g h) (ul Ic)

  pkg = product-map (comp k g) Ic
  pgh = product-map (comp g h) Ic
  ilk = injl-product-map k Ic

  -- the LHS (injl sees the inner associator path)
  lhs-l : ccr injl (product-map-eq1 (idMap C) (composeA k g h))
        ≡ ilkgh ∙ ccl injl (composeA k g h) ∙ ilkgh' ⁻¹
  lhs-l = ccr-il-pme1 Ic (composeA k g h)

  rhs-dist-l : ccr injl (prodpent-rhs-C k g h)
             ≡ ccr injl cp1 ∙ (ccr injl cp2 ∙ (ccr injl cp3 ∙ (ccr injl cp4
                 ∙ (ccr injl cp5 ∙ (ccr injl cp6 ∙ ccr injl cp7)))))
  rhs-dist-l = Distribute.dist k g h injl

  -- the seven face projections (each = one §4f lemma)
  prj1-l : ccr injl cp1 ≡ ilkgh ∙ ilkgh-II ⁻¹
  prj1-l = ccr-il-pme2 (comp (comp k g) h) (sy (ul Ic))

  prj2-l : ccr injl cp2 ≡ pmc-legl h (comp k g) Ic Ic
  prj2-l = pmc-injl h (comp k g) Ic Ic

  prj3-l : ccr injl cp3
         ≡ (composeA injl pkg ph) ⁻¹ ∙ ccl ph (ccr injl X3) ∙ composeA injl (comp pk pg) ph
  prj3-l = ccr-il-ccl ph X3

  prj4-l : ccr injl cp4
         ≡ (composeA injl (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injl pk pg)) ⁻¹
             ∙ composeA (comp injl pk) pg ph ∙ composeA injl pk (comp pg ph)
  prj4-l = ccr-il-composeA pk pg ph

  prj5-l : ccr injl cp5
         ≡ ((composeA injl pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) ilk)
              ∙ composeA k injl (comp pg ph))
           ∙ ccr k (ccr injl X5)
           ∙ ((composeA k injl pgh ⁻¹ ∙ (ccl pgh ilk) ⁻¹) ∙ composeA injl pk pgh)
  prj5-l = ccr-il-ccr-pm-C k X5

  prj6-l : ccr injl cp6 ≡ (pmc-legl (comp g h) k Ic Ic) ⁻¹
  prj6-l = ap-⁻¹ (comp injl) (pmc (comp g h) k Ic Ic)
         ∙ ap _⁻¹ (pmc-injl (comp g h) k Ic Ic)

  prj7-l : ccr injl cp7 ≡ (ilkgh' ∙ ilkgh'-II ⁻¹) ⁻¹
  prj7-l = ap-⁻¹ (comp injl) (product-map-eq2 (comp k (comp g h)) (sy (ul Ic)))
         ∙ ap _⁻¹ (ccr-il-pme2 (comp k (comp g h)) (sy (ul Ic)))

  -- the fully projected telescope (= `projected-l`'s RHS)
  Tel-l : comp injl (product-map (comp (comp k g) h) Ic)
        ≡ comp injl (product-map (comp k (comp g h)) Ic)
  Tel-l =
      (ilkgh ∙ ilkgh-II ⁻¹)
    ∙ (pmc-legl h (comp k g) Ic Ic
    ∙ (((composeA injl pkg ph) ⁻¹ ∙ ccl ph (ccr injl X3) ∙ composeA injl (comp pk pg) ph)
    ∙ (((composeA injl (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injl pk pg)) ⁻¹
          ∙ composeA (comp injl pk) pg ph ∙ composeA injl pk (comp pg ph))
    ∙ ((((composeA injl pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) ilk)
            ∙ composeA k injl (comp pg ph))
          ∙ ccr k (ccr injl X5)
          ∙ ((composeA k injl pgh ⁻¹ ∙ (ccl pgh ilk) ⁻¹) ∙ composeA injl pk pgh))
    ∙ ((pmc-legl (comp g h) k Ic Ic) ⁻¹
    ∙ ((ilkgh' ∙ ilkgh'-II ⁻¹) ⁻¹))))))

  projected-l :
      ccr injl cp1 ∙ (ccr injl cp2 ∙ (ccr injl cp3 ∙ (ccr injl cp4
        ∙ (ccr injl cp5 ∙ (ccr injl cp6 ∙ ccr injl cp7)))))
    ≡ Tel-l
  projected-l =
    ∙-cong prj1-l (∙-cong prj2-l (∙-cong prj3-l (∙-cong prj4-l
      (∙-cong prj5-l (∙-cong prj6-l prj7-l)))))

  -- ====================================================================
  -- Collapse Tel-l.  Inner expansions first (analogues of injr qX3c/qX5c,
  -- but SHORTER — injl's pme2 has no middle term).
  -- ====================================================================
  ilkg    = injl-product-map (comp k g) Ic
  ilkg-II = injl-product-map (comp k g) (comp Ic Ic)
  ilg     = injl-product-map g Ic
  ilh     = injl-product-map h Ic
  ilgh    = injl-product-map (comp g h) Ic
  ilgh-II = injl-product-map (comp g h) (comp Ic Ic)

  -- pmc-legl atoms (6 each, incl. associators).  For X3: pmc-legl g k Ic Ic;
  -- for X5: pmc-legl h g Ic Ic.
  a2 = composeA k g (injl {C1} {C})
  a3 = ccr k (ilg ⁻¹)
  a4 = (composeA k (injl {C2} {C}) pg) ⁻¹
  a5 = ccl pg (ilk ⁻¹)
  a6 = composeA (injl {D} {C}) pk pg
  b2 = composeA g h (injl {C0} {C})
  b3 = ccr g (ilh ⁻¹)
  b4 = (composeA g (injl {C1} {C}) ph) ⁻¹
  b5 = ccl ph (ilg ⁻¹)
  b6 = composeA (injl {C2} {C}) pg ph

  qX3-l : ccr injl X3 ≡ (ilkg ∙ ilkg-II ⁻¹) ∙ pmc-legl g k Ic Ic
  qX3-l = ap-∙ (comp injl) (product-map-eq2 (comp k g) (sy (ul Ic))) (pmc g k Ic Ic)
        ∙ ∙-cong (ccr-il-pme2 (comp k g) (sy (ul Ic))) (pmc-injl g k Ic Ic)

  qX3c-l : ccr injl X3 ≡ ilkg ∙ (a2 ∙ (a3 ∙ (a4 ∙ (a5 ∙ a6))))
  qX3c-l = qX3-l
         ∙ solveR
             ((ι ilkg ⊕ ι (ilkg-II ⁻¹)) ⊕ (((((ι ilkg-II ⊕ ι a2) ⊕ ι a3) ⊕ ι a4) ⊕ ι a5) ⊕ ι a6))
             (ι ilkg ⊕ (ι (ilkg-II ⁻¹) ⊕ (ι ilkg-II ⊕ (ι a2 ⊕ (ι a3 ⊕ (ι a4 ⊕ (ι a5 ⊕ ι a6)))))))
             (refl _)
         ∙ ap (ilkg ∙_) (cancL ilkg-II (a2 ∙ (a3 ∙ (a4 ∙ (a5 ∙ a6)))))

  qX5-l : ccr injl X5 ≡ (pmc-legl h g Ic Ic) ⁻¹ ∙ (ilgh-II ∙ ilgh ⁻¹)
  qX5-l = ap-∙ (comp injl) (sy (pmc h g Ic Ic)) (product-map-eq2 (comp g h) (ul Ic))
        ∙ ∙-cong (ap-⁻¹ (comp injl) (pmc h g Ic Ic) ∙ ap _⁻¹ (pmc-injl h g Ic Ic))
                 (ccr-il-pme2 (comp g h) (ul Ic))

  qX5c-l : ccr injl X5 ≡ b6 ⁻¹ ∙ (b5 ⁻¹ ∙ (b4 ⁻¹ ∙ (b3 ⁻¹ ∙ (b2 ⁻¹ ∙ ilgh ⁻¹))))
  qX5c-l = qX5-l
         ∙ ap (_∙ (ilgh-II ∙ ilgh ⁻¹)) (invflat6 ilgh-II b2 b3 b4 b5 b6)
         ∙ solveR
             ((ι (b6 ⁻¹) ⊕ (ι (b5 ⁻¹) ⊕ (ι (b4 ⁻¹) ⊕ (ι (b3 ⁻¹) ⊕ (ι (b2 ⁻¹) ⊕ ι (ilgh-II ⁻¹))))))
               ⊕ (ι ilgh-II ⊕ ι (ilgh ⁻¹)))
             (ι (b6 ⁻¹) ⊕ (ι (b5 ⁻¹) ⊕ (ι (b4 ⁻¹) ⊕ (ι (b3 ⁻¹) ⊕ (ι (b2 ⁻¹) ⊕ (ι (ilgh-II ⁻¹) ⊕ (ι ilgh-II ⊕ ι (ilgh ⁻¹))))))))
             (refl _)
         ∙ ap (λ z → b6 ⁻¹ ∙ (b5 ⁻¹ ∙ (b4 ⁻¹ ∙ (b3 ⁻¹ ∙ (b2 ⁻¹ ∙ z))))) (cancL ilgh-II (ilgh ⁻¹))

  -- ====================================================================
  -- tel-collapse-l, PROVED (mirrors InjrFactor; closes by ONE pentagon).
  -- (A) tel-free-l flattens Tel-l to ilkgh ∙ (N ∙ ilkgh'⁻¹).
  -- (B) N ≡ ccl injl (composeA k g h) via CPS + pentagonator k g h injl.
  -- ====================================================================

  -- survivor atoms of N (injl analog of M's m2..m13; NO u atoms)
  nc2  = composeA (comp k g) h (injl {C0} {C})
  nc3  = ccr (comp k g) (ilh ⁻¹)
  nc4  = (composeA (comp k g) (injl {C1} {C}) ph) ⁻¹
  nc5  = ccl ph (ilkg ⁻¹)
  m6l  = ccl ph (ccr injl X3)
  nc7  = (ccl ph (composeA (injl {D} {C}) pk pg)) ⁻¹
  nc8  = composeA (comp (injl {D} {C}) pk) pg ph
  nc9  = ccl (comp pg ph) ilk
  nc10 = composeA k (injl {C2} {C}) (comp pg ph)
  m11l = ccr k (ccr injl X5)
  nc12 = (ccr k (ilgh ⁻¹)) ⁻¹
  nc13 = (composeA k (comp g h) (injl {C0} {C})) ⁻¹

  N : comp (comp (comp k g) h) injl ≡ comp (comp k (comp g h)) injl
  N = nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ (m6l ∙ (nc7 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ (m11l ∙ (nc12 ∙ nc13))))))))))

  Nflat : comp injl (product-map (comp (comp k g) h) Ic)
        ≡ comp injl (product-map (comp k (comp g h)) Ic)
  Nflat = ilkgh ∙ (nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ (m6l ∙ (nc7 ∙ (nc8 ∙ (nc9 ∙ (nc10
            ∙ (m11l ∙ (nc12 ∙ (nc13 ∙ ilkgh' ⁻¹))))))))))))

  -- blocks of Tel-l (decompose definitionally; bl1/bl7 have NO unitor middle)
  bl1 = ilkgh ∙ ilkgh-II ⁻¹
  bl2 = pmc-legl h (comp k g) Ic Ic
  bl3 = ((composeA injl pkg ph) ⁻¹ ∙ ccl ph (ccr injl X3)) ∙ composeA injl (comp pk pg) ph
  bl4 = (((composeA injl (comp pk pg) ph) ⁻¹ ∙ (ccl ph (composeA injl pk pg)) ⁻¹)
          ∙ composeA (comp injl pk) pg ph) ∙ composeA injl pk (comp pg ph)
  bl5 = (((composeA injl pk (comp pg ph) ⁻¹ ∙ ccl (comp pg ph) ilk)
            ∙ composeA k injl (comp pg ph)) ∙ ccr k (ccr injl X5))
          ∙ ((composeA k injl pgh ⁻¹ ∙ (ccl pgh ilk) ⁻¹) ∙ composeA injl pk pgh)
  bl6 = (pmc-legl (comp g h) k Ic Ic) ⁻¹
  bl7 = (ilkgh' ∙ ilkgh'-II ⁻¹) ⁻¹

  tel-decomp-l : Tel-l ≡ bl1 ∙ (bl2 ∙ (bl3 ∙ (bl4 ∙ (bl5 ∙ (bl6 ∙ bl7)))))
  tel-decomp-l = refl _

  -- cancellation pivots (block boundaries) + involution rewrites
  jl1   = ilkgh-II
  jl2   = ilkgh'-II
  pl9   = composeA injl pkg ph
  pl12  = composeA injl (comp pk pg) ph
  pl16  = composeA injl pk (comp pg ph)
  pl23  = composeA injl pk pgh
  pApl  = composeA k (injl {C2} {C}) pgh
  pclkl = ccl pgh ilk
  e6l   = (ccl pgh (ilk ⁻¹)) ⁻¹
  d6l   = ((composeA k (injl {C2} {C}) pgh) ⁻¹) ⁻¹

  e6l-pclkl : e6l ≡ pclkl
  e6l-pclkl = ap _⁻¹ (ap-⁻¹ (λ m → comp m pgh) ilk) ∙ inv-inv pclkl

  d6l-pApl : d6l ≡ pApl
  d6l-pApl = inv-inv pApl

  b7flat-l : bl7 ≡ jl2 ∙ ilkgh' ⁻¹
  b7flat-l = inv-∙ ilkgh' (ilkgh'-II ⁻¹) ∙ ap (_∙ ilkgh' ⁻¹) (inv-inv ilkgh'-II)

  -- tails of the fully-flattened Tel-l (TelFlat) for the cancellation sweep
  TEt = e6l ∙ (d6l ∙ (nc12 ∙ (nc13 ∙ (jl2 ⁻¹ ∙ (jl2 ∙ ilkgh' ⁻¹)))))
  TDt = nc9 ∙ (nc10 ∙ (m11l ∙ (pApl ⁻¹ ∙ (pclkl ⁻¹ ∙ (pl23 ∙ (pl23 ⁻¹ ∙ TEt))))))
  TCt = nc7 ∙ (nc8 ∙ (pl16 ∙ (pl16 ⁻¹ ∙ TDt)))
  TBt = m6l ∙ (pl12 ∙ (pl12 ⁻¹ ∙ TCt))
  TAt = nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ (pl9 ∙ (pl9 ⁻¹ ∙ TBt)))))

  Ninner : comp (comp (comp k g) h) injl ≡ comp injl (product-map (comp k (comp g h)) Ic)
  Ninner = nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ (m6l ∙ (nc7 ∙ (nc8 ∙ (nc9 ∙ (nc10
             ∙ (m11l ∙ (nc12 ∙ (nc13 ∙ ilkgh' ⁻¹)))))))))))

  T6c : pApl ⁻¹ ∙ (pclkl ⁻¹ ∙ TEt) ≡ nc12 ∙ (nc13 ∙ ilkgh' ⁻¹)
  T6c =
      ap (λ w → pApl ⁻¹ ∙ (pclkl ⁻¹ ∙ (w ∙ (d6l ∙ (nc12 ∙ (nc13 ∙ (jl2 ⁻¹ ∙ (jl2 ∙ ilkgh' ⁻¹)))))))) e6l-pclkl
    ∙ ap (pApl ⁻¹ ∙_) (cancL pclkl (d6l ∙ (nc12 ∙ (nc13 ∙ (jl2 ⁻¹ ∙ (jl2 ∙ ilkgh' ⁻¹))))))
    ∙ ap (λ w → pApl ⁻¹ ∙ (w ∙ (nc12 ∙ (nc13 ∙ (jl2 ⁻¹ ∙ (jl2 ∙ ilkgh' ⁻¹)))))) d6l-pApl
    ∙ cancL pApl (nc12 ∙ (nc13 ∙ (jl2 ⁻¹ ∙ (jl2 ∙ ilkgh' ⁻¹))))
    ∙ ap (λ z → nc12 ∙ (nc13 ∙ z)) (cancL jl2 (ilkgh' ⁻¹))

  TDc : TDt ≡ nc9 ∙ (nc10 ∙ (m11l ∙ (nc12 ∙ (nc13 ∙ ilkgh' ⁻¹))))
  TDc =
      ap (λ z → nc9 ∙ (nc10 ∙ (m11l ∙ (pApl ⁻¹ ∙ (pclkl ⁻¹ ∙ z))))) (cancR pl23 TEt)
    ∙ ap (λ z → nc9 ∙ (nc10 ∙ (m11l ∙ z))) T6c

  TCc : TCt ≡ nc7 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ (m11l ∙ (nc12 ∙ (nc13 ∙ ilkgh' ⁻¹))))))
  TCc =
      ap (λ z → nc7 ∙ (nc8 ∙ z)) (cancR pl16 TDt)
    ∙ ap (λ z → nc7 ∙ (nc8 ∙ z)) TDc

  TBc : TBt ≡ m6l ∙ (nc7 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ (m11l ∙ (nc12 ∙ (nc13 ∙ ilkgh' ⁻¹)))))))
  TBc =
      ap (m6l ∙_) (cancR pl12 TCt)
    ∙ ap (m6l ∙_) TCc

  TAc : TAt ≡ Ninner
  TAc =
      ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ z)))) (cancR pl9 TBt)
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (nc5 ∙ z)))) TBc

  tel-free-l : Tel-l ≡ Nflat
  tel-free-l =
      ap (λ z → bl1 ∙ (bl2 ∙ (bl3 ∙ (bl4 ∙ (bl5 ∙ z)))))
         (∙-cong (invflat6 jl2 (composeA k (comp g h) (injl {C0} {C})) (ccr k (ilgh ⁻¹))
                            ((composeA k (injl {C2} {C}) pgh) ⁻¹) (ccl pgh (ilk ⁻¹)) pl23)
                 b7flat-l)
    ∙ solveR
        ((ι ilkgh ⊕ ι (jl1 ⁻¹))
          ⊕ (((((ι jl1 ⊕ ι nc2) ⊕ ι nc3) ⊕ ι nc4) ⊕ ι nc5) ⊕ ι pl9)
          ⊕ ((ι (pl9 ⁻¹) ⊕ ι m6l) ⊕ ι pl12)
          ⊕ (((ι (pl12 ⁻¹) ⊕ ι nc7) ⊕ ι nc8) ⊕ ι pl16)
          ⊕ ((((ι (pl16 ⁻¹) ⊕ ι nc9) ⊕ ι nc10) ⊕ ι m11l) ⊕ ((ι (pApl ⁻¹) ⊕ ι (pclkl ⁻¹)) ⊕ ι pl23))
          ⊕ (ι (pl23 ⁻¹) ⊕ (ι e6l ⊕ (ι d6l ⊕ (ι nc12 ⊕ (ι nc13 ⊕ ι (jl2 ⁻¹))))))
          ⊕ (ι jl2 ⊕ ι (ilkgh' ⁻¹)))
        (ι ilkgh ⊕ ι (jl1 ⁻¹) ⊕ ι jl1 ⊕ ι nc2 ⊕ ι nc3 ⊕ ι nc4 ⊕ ι nc5 ⊕ ι pl9 ⊕ ι (pl9 ⁻¹)
          ⊕ ι m6l ⊕ ι pl12 ⊕ ι (pl12 ⁻¹) ⊕ ι nc7 ⊕ ι nc8 ⊕ ι pl16 ⊕ ι (pl16 ⁻¹)
          ⊕ ι nc9 ⊕ ι nc10 ⊕ ι m11l ⊕ ι (pApl ⁻¹) ⊕ ι (pclkl ⁻¹) ⊕ ι pl23 ⊕ ι (pl23 ⁻¹)
          ⊕ ι e6l ⊕ ι d6l ⊕ ι nc12 ⊕ ι nc13 ⊕ ι (jl2 ⁻¹) ⊕ ι jl2 ⊕ ι (ilkgh' ⁻¹))
        (refl _)
    ∙ ap (ilkgh ∙_) (cancL jl1 TAt)
    ∙ ap (ilkgh ∙_) TAc

  -- ====================================================================
  -- (B) N ≡ ccl injl (composeA k g h).  Expand the folded X3/X5 cells,
  -- cancel the inner IR-pairs (Nred → GCl), then collapse GCl by the CPS
  -- moves (cn1-n/pent-expand/cn2-collapse/pent-cps/cn3-collapse) and ONE
  -- pentagonator (Rocq `injl_factor_dsl` `Pccl`).
  -- ====================================================================

  -- distributed inner expansions of the two folded sub-projections
  cpilkg = ccl ph ilkg
  cpa2 = ccl ph a2
  cpa3 = ccl ph a3
  cpa4 = ccl ph a4
  cpa5 = ccl ph a5
  cpa6 = ccl ph a6
  ckb6 = ccr k (b6 ⁻¹)
  ckb5 = ccr k (b5 ⁻¹)
  ckb4 = ccr k (b4 ⁻¹)
  ckb3 = ccr k (b3 ⁻¹)
  ckb2 = ccr k (b2 ⁻¹)
  ckilgh = ccr k (ilgh ⁻¹)

  m6l-f : m6l ≡ cpilkg ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ cpa6))))
  m6l-f = ap (ccl ph) qX3c-l ∙ apdist6 (λ m → comp m ph) ilkg a2 a3 a4 a5 a6

  m11l-f : m11l ≡ ckb6 ∙ (ckb5 ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ ckilgh))))
  m11l-f = ap (ccr k) qX5c-l ∙ apdist6 (comp k) (b6 ⁻¹) (b5 ⁻¹) (b4 ⁻¹) (b3 ⁻¹) (b2 ⁻¹) (ilgh ⁻¹)

  -- normalised m11 atoms (strip the double inverses)
  ckb6n = (ccr k b6) ⁻¹
  ckb5n = ccr k (ccl ph ilg)
  ckb4n = ccr k (composeA g (injl {C1} {C}) ph)
  ckb3n = ccr k (ccr g ilh)
  ckb2n = (ccr k b2) ⁻¹

  ckb6≡ : ckb6 ≡ ckb6n
  ckb6≡ = ap-⁻¹ (comp k) b6
  ckb5≡ : ckb5 ≡ ckb5n
  ckb5≡ = ap (ccr k) (ap _⁻¹ (ap-⁻¹ (λ m → comp m ph) ilg) ∙ inv-inv (ccl ph ilg))
  ckb4≡ : ckb4 ≡ ckb4n
  ckb4≡ = ap (ccr k) (inv-inv (composeA g (injl {C1} {C}) ph))
  ckb3≡ : ckb3 ≡ ckb3n
  ckb3≡ = ap (ccr k) (ap _⁻¹ (ap-⁻¹ (comp g) ilh) ∙ inv-inv (ccr g ilh))
  ckb2≡ : ckb2 ≡ ckb2n
  ckb2≡ = ap-⁻¹ (comp k) b2

  -- tail of N during the X5-region cancellation
  T7l = nc8 ∙ (nc9 ∙ (nc10 ∙ (m11l ∙ (nc12 ∙ nc13))))

  -- red56-l : m5/m6/m7 region — nc5 kills m6l's lead, m6l's tail kills nc7
  red56-l : nc5 ∙ (m6l ∙ (nc7 ∙ T7l)) ≡ cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ T7l)))
  red56-l =
      ap (λ z → nc5 ∙ (z ∙ (nc7 ∙ T7l))) m6l-f
    ∙ solveR
        (ι nc5 ⊕ ((ι cpilkg ⊕ (ι cpa2 ⊕ (ι cpa3 ⊕ (ι cpa4 ⊕ (ι cpa5 ⊕ ι cpa6))))) ⊕ (ι nc7 ⊕ ι T7l)))
        (ι nc5 ⊕ (ι cpilkg ⊕ (ι cpa2 ⊕ (ι cpa3 ⊕ (ι cpa4 ⊕ (ι cpa5 ⊕ (ι cpa6 ⊕ (ι nc7 ⊕ ι T7l))))))))
        (refl _)
    ∙ ap (_∙ (cpilkg ∙ REST6)) (ap-⁻¹ (λ m → comp m ph) ilkg)
    ∙ cancL cpilkg REST6
    ∙ ap (λ z → cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ z)))) (cancR cpa6 T7l)
    where
    REST6 = cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ (cpa6 ∙ (nc7 ∙ T7l)))))

  -- red1112-l : m11/m12 region — m11l's last atom (ckilgh) kills nc12
  red1112-l : m11l ∙ (nc12 ∙ nc13) ≡ ckb6 ∙ (ckb5 ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ nc13))))
  red1112-l =
      ap (λ z → z ∙ (nc12 ∙ nc13)) m11l-f
    ∙ solveR
        ((ι ckb6 ⊕ (ι ckb5 ⊕ (ι ckb4 ⊕ (ι ckb3 ⊕ (ι ckb2 ⊕ ι ckilgh))))) ⊕ (ι nc12 ⊕ ι nc13))
        (ι ckb6 ⊕ (ι ckb5 ⊕ (ι ckb4 ⊕ (ι ckb3 ⊕ (ι ckb2 ⊕ (ι ckilgh ⊕ (ι nc12 ⊕ ι nc13)))))))
        (refl _)
    ∙ ap (λ z → ckb6 ∙ (ckb5 ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ z))))) (cancR ckilgh nc13)

  GCl : comp (comp (comp k g) h) injl ≡ comp (comp k (comp g h)) injl
  GCl = nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ (nc8 ∙ (nc9 ∙ (nc10
          ∙ (ckb6 ∙ (ckb5 ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ nc13))))))))))))))

  Nred : N ≡ GCl
  Nred =
      ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ z))) red56-l
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ z))))))))))
         red1112-l

  -- the CPS-collapse intermediate maps + tails
  Al = composeA (comp k (injl {C2} {C})) pg ph
  Bl = composeA k (comp (injl {C2} {C}) pg) ph
  Dl = composeA k (comp g (injl {C1} {C})) ph
  Gl = composeA k g (comp (injl {C1} {C}) ph)
  Hl = composeA k g (comp h (injl {C0} {C}))
  cAipgl = composeA k (injl {C2} {C}) pg

  RQc = ckb2n ∙ nc13
  RQb = ckb3n ∙ RQc
  RQa = ckb4n ∙ RQb
  RQl = ckb5n ∙ RQa
  RKl = ckb6n ∙ RQl

  GCln = nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ RKl)))))))))

  GCl≡GCln : GCl ≡ GCln
  GCl≡GCln =
    ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ (cpa5 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ z))))))))))
       ( ap (λ a → a ∙ (ckb5 ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ nc13))))) ckb6≡
       ∙ ap (λ b → ckb6n ∙ (b ∙ (ckb4 ∙ (ckb3 ∙ (ckb2 ∙ nc13))))) ckb5≡
       ∙ ap (λ c → ckb6n ∙ (ckb5n ∙ (c ∙ (ckb3 ∙ (ckb2 ∙ nc13))))) ckb4≡
       ∙ ap (λ d → ckb6n ∙ (ckb5n ∙ (ckb4n ∙ (d ∙ (ckb2 ∙ nc13))))) ckb3≡
       ∙ ap (λ e → ckb6n ∙ (ckb5n ∙ (ckb4n ∙ (ckb3n ∙ (e ∙ nc13))))) ckb2≡ )

  -- (1) irk pair: cn1-n collapses cpa5 ∙ nc8, then nc9's inverse meets nc10
  red-irk-l : cpa5 ∙ (nc8 ∙ (nc9 ∙ (nc10 ∙ RKl))) ≡ Al ∙ (nc10 ∙ RKl)
  red-irk-l =
      cn1-n pg ph (ilk ⁻¹) (nc9 ∙ (nc10 ∙ RKl))
    ∙ ap (Al ∙_)
        ( ap (_∙ (nc9 ∙ (nc10 ∙ RKl))) (ap-⁻¹ (λ m → comp m (comp pg ph)) ilk)
        ∙ cancL nc9 (nc10 ∙ RKl) )

  -- (2) pent leg + cancel cpa4 / ckb6n
  red-pent-l : cpa4 ∙ (Al ∙ (nc10 ∙ RKl)) ≡ Bl ∙ RQl
  red-pent-l =
      ap (λ z → z ∙ (Al ∙ (nc10 ∙ RKl))) (ap-⁻¹ (λ m → comp m ph) cAipgl)
    ∙ ap ((ccl ph cAipgl) ⁻¹ ∙_) (pent-expand k injl pg ph RKl)
    ∙ ap (λ z → (ccl ph cAipgl) ⁻¹ ∙ (ccl ph cAipgl ∙ (Bl ∙ z))) (cancR (ccr k b6) RQl)
    ∙ cancL (ccl ph cAipgl) (Bl ∙ RQl)

  -- (3) irg pair: cn2-collapse
  red-irg-l : cpa3 ∙ (Bl ∙ RQl) ≡ Dl ∙ RQa
  red-irg-l = cn2-collapse k ph ilg RQa

  -- (4) pentagon leg (forward, as pent-cps)
  red-pent-cps-l : nc4 ∙ (cpa2 ∙ (Dl ∙ RQa)) ≡ Gl ∙ RQb
  red-pent-cps-l = pent-cps k g injl ph RQb

  -- (5) irh pair: cn3-collapse
  red-irh-l : nc3 ∙ (Gl ∙ RQb) ≡ Hl ∙ RQc
  red-irh-l = cn3-collapse k g ilh RQc

  -- (6) the genuine pentagon: nc2/Hl/ckb2n/nc13 = the re-leg by pentagonator
  Pp = ccl (injl {C0} {C}) (composeA k g h)
  Qp = composeA k (comp g h) (injl {C0} {C})
  Rp = ccr k (composeA g h (injl {C0} {C}))

  Pccl : nc2 ∙ (Hl ∙ (ckb2n ∙ nc13)) ≡ ccl injl (composeA k g h)
  Pccl =
      solveR (ι nc2 ⊕ (ι Hl ⊕ (ι ckb2n ⊕ ι nc13)))
             ((ι nc2 ⊕ ι Hl) ⊕ (ι ckb2n ⊕ ι nc13))
             (refl _)
    ∙ ap (_∙ (ckb2n ∙ nc13)) (pentagonator k g h (injl {C0} {C}))
    ∙ solveR (((ι Pp ⊕ ι Qp) ⊕ ι Rp) ⊕ (ι ckb2n ⊕ ι nc13))
             (ι Pp ⊕ (ι Qp ⊕ (ι Rp ⊕ (ι ckb2n ⊕ ι nc13))))
             (refl _)
    ∙ ap (λ z → Pp ∙ (Qp ∙ z)) (cancR Rp nc13)
    ∙ ap (Pp ∙_) (right-inv Qp)
    ∙ right-unit Pp

  GCl-collapse : GCl ≡ ccl injl (composeA k g h)
  GCl-collapse =
      GCl≡GCln
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ (cpa4 ∙ z)))))) red-irk-l
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ (cpa3 ∙ z))))) red-pent-l
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ (nc4 ∙ (cpa2 ∙ z)))) red-irg-l
    ∙ ap (λ z → nc2 ∙ (nc3 ∙ z)) red-pent-cps-l
    ∙ ap (λ z → nc2 ∙ z) red-irh-l
    ∙ Pccl

  N-collapse : N ≡ ccl injl (composeA k g h)
  N-collapse = Nred ∙ GCl-collapse

  regroup-l : Ninner ≡ N ∙ ilkgh' ⁻¹
  regroup-l =
    solveR
      (ι nc2 ⊕ ι nc3 ⊕ ι nc4 ⊕ ι nc5 ⊕ ι m6l ⊕ ι nc7 ⊕ ι nc8 ⊕ ι nc9 ⊕ ι nc10
        ⊕ ι m11l ⊕ ι nc12 ⊕ ι nc13 ⊕ ι (ilkgh' ⁻¹))
      ((ι nc2 ⊕ (ι nc3 ⊕ (ι nc4 ⊕ (ι nc5 ⊕ (ι m6l ⊕ (ι nc7 ⊕ (ι nc8 ⊕ (ι nc9 ⊕ (ι nc10
        ⊕ (ι m11l ⊕ (ι nc12 ⊕ ι nc13)))))))))) ) ⊕ ι (ilkgh' ⁻¹))
      (refl _)

  -- the genuine pentagon kernel: the projected telescope collapses to the
  -- inner-associator leg, by ONE pentagonator (Rocq `injl_factor_dsl` `Pccl`).
  tel-collapse-l : Tel-l ≡ ilkgh ∙ ccl injl (composeA k g h) ∙ ilkgh' ⁻¹
  tel-collapse-l =
      tel-free-l
    ∙ ap (ilkgh ∙_) regroup-l
    ∙ ap (ilkgh ∙_) (ap (_∙ ilkgh' ⁻¹) N-collapse)
    ∙ (∙-assoc ilkgh (ccl injl (composeA k g h)) (ilkgh' ⁻¹)) ⁻¹

  collapse-l : ccr injl (prodpent-rhs-C k g h)
             ≡ ilkgh ∙ ccl injl (composeA k g h) ∙ ilkgh' ⁻¹
  collapse-l = rhs-dist-l ∙ projected-l ∙ tel-collapse-l

prod-pent-C-injl : {C0 C1 C2 D C : Cat}
                   (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1)
                 → ccr injl (product-map-eq1 (idMap C) (composeA k g h))
                 ≡ ccr injl (prodpent-rhs-C k g h)
prod-pent-C-injl k g h = InjlFactor.lhs-l k g h ∙ (InjlFactor.collapse-l k g h) ⁻¹

------------------------------------------------------------------------
-- §7  prod-pent-C: assemble the two factors (Rocq `prod_pent_C`).
------------------------------------------------------------------------

prod-pent-C : {C0 C1 C2 D C : Cat}
              (k : Map C2 D) (g : Map C1 C2) (h : Map C0 C1)
            → product-map-eq1 (idMap C) (composeA k g h)
            ≡ prodpent-rhs-C k g h
prod-pent-C k g h =
  prod-path-eq _ _ (prod-pent-C-injl k g h) (prod-pent-C-injr k g h)
