{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — STREAM B: − ×c 𝕀 PRESERVES PUSHOUTS
-- (Rocq `times_I_preserves`, Main.v 6277).
--
-- MODULAR structure: the generic machinery (`equiv-from-homotopy`,
-- `inv-equiv`) and the leaf coherence `uncurry-precomp` (from `pmc`-free
-- pairing laws) are PROVED here.  The two structural/coherence leaves are
-- isolated behind a thin interface:
--   * `cone-reshuffle`  — the fibered equivalence  sq-cone S (Fun 𝕀 X)
--                          ≃ sq-cone (times-I S) X  (Rocq `cone_reshuffle`);
--   * `times-I-factor`  — the comparison factors through it
--                          (Rocq `times_I_comparison_factor` = `abstract_helper`,
--                          the pmc / prod-pent-C telescope).
-- `times-I-preserves` is then a clean assembly: the comparison for T×𝕀 is
-- homotopic to the composite of three equivalences (curry ; comparison at
-- Fun 𝕀 X ; cone-reshuffle), hence an equivalence.
------------------------------------------------------------------------

module TimesI where

open import Spartan
open import CatAxioms
open import Coherence
open import Constructions using (equiv-inv)
open import HigherCat using (𝕀; equiv-inj)
open import Pullbacks using (_×c_; π₁; π₂; ⟨_,_⟩; pair-β₁; pair-β₂;
                            equiv-inv-rinv; equiv-inv-linv)
open import Product using (product-map; injl-product-map; injr-product-map;
                          mp-equiv-inj; retract-path-inj;
                          ipe; pmc; product-map-eq1; product-map-eq2;
                          prodpent-rhs-C; prod-pent-C)
open import Exponentials using (Fun; ev; exp-comparison; exp-equiv)
open import Interval using (invertible-to-equiv; equiv-comp)
open import SigmaEquiv using (Σ-change-of-base; Σ-fiberwise-equiv;
                             post-comp-path-equiv; pre-comp-path-equiv)
open import CayleyAssoc
open import SquareAlg

------------------------------------------------------------------------
-- §0  generic equivalence machinery
------------------------------------------------------------------------

-- the inverse of an equivalence is an equivalence
inv-equiv : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → B ≃ A
inv-equiv e =
  equiv-inv e ,
  invertible-to-equiv (equiv-inv e)
    (pr₁ e , equiv-inv-linv e , equiv-inv-rinv e)

-- a map homotopic to an equivalence is an equivalence
equiv-from-homotopy : {A : Type 𝓤} {B : Type 𝓥} (f g : A → B)
  → ((x : A) → f x ≡ g x) → is-equiv g → is-equiv f
equiv-from-homotopy f g hom eg =
  invertible-to-equiv f
    ( equiv-inv (g , eg)
    , (λ y → hom (equiv-inv (g , eg) y) ∙ equiv-inv-rinv (g , eg) y)
    , (λ x → ap (equiv-inv (g , eg)) (hom x) ∙ equiv-inv-linv (g , eg) x) )

-- product of two equivalences
prod-equiv : {A A' B B' : Type 𝓤} → A ≃ A' → B ≃ B' → (A × B) ≃ (A' × B')
prod-equiv ea eb =
  (λ ab → pr₁ ea (pr₁ ab) , pr₁ eb (pr₂ ab)) ,
  invertible-to-equiv _
    ( (λ a'b' → equiv-inv ea (pr₁ a'b') , equiv-inv eb (pr₂ a'b'))
    , (λ a'b' → to-×-≡ (equiv-inv-rinv ea (pr₁ a'b')) (equiv-inv-rinv eb (pr₂ a'b')))
    , (λ ab → to-×-≡ (equiv-inv-linv ea (pr₁ ab)) (equiv-inv-linv eb (pr₂ ab))) )

-- ap of an equivalence is an equivalence on path spaces (an equiv is an
-- embedding): inverse `equiv-inj`, round-trips from `mp-equiv-inj` (Product)
-- and `retract-path-inj` (with `equiv-inv` as the retraction).
ap-equiv : {A B : Type 𝓤} (e : A ≃ B) {x y : A}
         → (x ≡ y) ≃ (pr₁ e x ≡ pr₁ e y)
ap-equiv e {x} {y} =
  ap (pr₁ e) ,
  invertible-to-equiv (ap (pr₁ e))
    ( equiv-inj (pr₁ e) (pr₂ e)
    , (λ q → mp-equiv-inj (pr₁ e) (pr₂ e) q)
    , (λ p → retract-path-inj (pr₁ e) (equiv-inv e) (equiv-inv-linv e)
               (equiv-inj (pr₁ e) (pr₂ e) (ap (pr₁ e) p)) p
               (mp-equiv-inj (pr₁ e) (pr₂ e) (ap (pr₁ e) p))) )

------------------------------------------------------------------------
-- §1  uncurry-precomp (Rocq `uncurry_precomp`):  the exponential
--     comparison is natural in the first argument.  PROVED from the
--     pairing naturality + the product-map projection laws.
------------------------------------------------------------------------

-- the pairing↔product-map bridge (Rocq `uncurry_def`: uncurry u = ev ∘ product_map u Id).
-- Here `exp-comparison` is pairing-based, so this is a genuine (small) lemma via `ipe`.
uncurry-bridge : {A B X : Cat} (u : Map X (Fun A B))
  → exp-comparison A B X u ≡ comp (ev A B) (product-map u (idMap A))
uncurry-bridge {A} {B} {X} u =
  ap (comp (ev A B))
    (ipe ⟨ comp u (π₁ X A) , π₂ X A ⟩ (product-map u (idMap A))
      (pair-β₁ (comp u (π₁ X A)) (π₂ X A) ∙ (injl-product-map u (idMap A)) ⁻¹)
      (pair-β₂ (comp u (π₁ X A)) (π₂ X A)
        ∙ (comp-id-l (π₂ X A)) ⁻¹ ∙ (injr-product-map u (idMap A)) ⁻¹))

-- uncurry-precomp in pmc-form (= Rocq `uncurry_precomp_def`), via the bridge.
uncurry-precomp : {A B Xc W : Cat} (φ : Map W Xc) (k : Map Xc (Fun A B))
  → exp-comparison A B W (comp k φ)
  ≡ comp (exp-comparison A B Xc k) (product-map φ (idMap A))
uncurry-precomp {A} {B} {Xc} {W} φ k =
    uncurry-bridge (comp k φ)
  ∙ ap (comp (ev A B)) (product-map-eq2 (comp k φ) ((comp-id-l (idMap A)) ⁻¹))
  ∙ ap (comp (ev A B)) (pmc φ k (idMap A) (idMap A))
  ∙ (composeA (ev A B) (product-map k (idMap A)) (product-map φ (idMap A))) ⁻¹
  ∙ ccl (product-map φ (idMap A)) ((uncurry-bridge k) ⁻¹)

------------------------------------------------------------------------
-- §1b  small path/product helpers for abstract_helper
------------------------------------------------------------------------

-- Rocq `cancl`.
cancl : {A : Type 𝓤} {x y z : A} (p : x ≡ y) (q : y ≡ z) → p ⁻¹ ∙ (p ∙ q) ≡ q
cancl (refl _) q = refl q

-- cancl through a single `ap` whisker (for the ccl-bridge pairs).
cancl-ap : {A : Type 𝓤} {B : Type 𝓥} (F : A → B) {x y : A} (p : x ≡ y)
           {z : B} (rest : F y ≡ z)
         → ap F (p ⁻¹) ∙ (ap F p ∙ rest) ≡ rest
cancl-ap F (refl _) rest = refl rest

-- cancl through a doubly-whiskered ccl (for the inner ccl pmh (ccl pmg _) pair).
cancl-ccl2 : {A B Cc Dd : Cat} (m : Map A B) (n : Map B Cc)
             {f f' : Map Cc Dd} (p : f ≡ f') {z : Map A Dd}
             (rest : comp (comp f' n) m ≡ z)
           → ccl m (ccl n (p ⁻¹)) ∙ (ccl m (ccl n p) ∙ rest) ≡ rest
cancl-ccl2 m n (refl _) rest = refl rest

-- Rocq `pentL` (also in ConeNat; re-proved locally to avoid a cube dependency).
pentL : {A B C D E : Cat} (f : Map D E) (g : Map C D) (hh : Map B C) (e : Map A B)
  → composeA (comp f g) hh e
  ≡ (ccl e (composeA f g hh) ∙ composeA f (comp g hh) e)
    ∙ ccr f (composeA g hh e)
    ∙ (composeA f g (comp hh e)) ⁻¹
pentL f g hh e =
    (right-unit (composeA (comp f g) hh e)) ⁻¹
  ∙ ap (λ z → composeA (comp f g) hh e ∙ z)
       ((right-inv (composeA f g (comp hh e))) ⁻¹)
  ∙ (∙-assoc (composeA (comp f g) hh e) (composeA f g (comp hh e))
             ((composeA f g (comp hh e)) ⁻¹)) ⁻¹
  ∙ ap (λ z → z ∙ (composeA f g (comp hh e)) ⁻¹) (pentagonator f g hh e)

-- Rocq `slideA`: collapse an interchange of two right-whiskered ccr's.
slideA : {A B Cc Dd : Cat} (f : Map Cc Dd) (c : Map A B)
  {a a' a'' : Map B Cc} (P : a ≡ a') (Q : a' ≡ a'')
  {y : Map A Dd} (rest : comp f (comp a'' c) ≡ y)
  → (composeA f a c) ⁻¹
    ∙ (ccl c (ccr f P) ∙ (ccl c (ccr f Q) ∙ (composeA f a'' c ∙ rest)))
  ≡ ap (λ w → comp f (comp w c)) (P ∙ Q) ∙ rest
slideA f c (refl a) (refl _) rest = cancl (composeA f a c) rest

-- Rocq `slideB`: slide a single left-whiskered ccr through a composeA.
slideB : {A B Cc Dd : Cat} (f : Map Cc Dd) (g : Map B Cc)
  {a a' : Map A B} (G : a ≡ a')
  {y : Map A Dd} (rest : comp f (comp g a') ≡ y)
  → (composeA f g a) ⁻¹ ∙ (ccr (comp f g) G ∙ (composeA f g a' ∙ rest))
  ≡ ap (λ w → comp f (comp g w)) G ∙ rest
slideB f g (refl a) rest = cancl (composeA f g a) rest

-- Rocq `product_map_eq1_inv`.
product-map-eq1-inv : {A B X Y : Cat} {f f' : Map A B} (g : Map X Y) (s : f ≡ f')
  → product-map-eq1 g (s ⁻¹) ≡ (product-map-eq1 g s) ⁻¹
product-map-eq1-inv g s = ap-⁻¹ (λ f → product-map f g) s

-- the product-map-eq exchange square (Rocq `product_map_eq_comm`).
product-map-eq-comm : {A B X Y : Cat} {f f' : Map A B} {g g' : Map X Y}
  (s : f ≡ f') (e : g ≡ g')
  → product-map-eq1 g s ∙ product-map-eq2 f' e
  ≡ product-map-eq2 f e ∙ product-map-eq1 g' s
product-map-eq-comm (refl _) (refl _) = refl _

-- Rocq `mpm`: merge two adjacent maponpaths-of-f in a chain.
mpm : {A : Type 𝓤} {B : Type 𝓥} (f : A → B) {a b c : A} (p : a ≡ b) (q : b ≡ c)
      {W : B} (r : f c ≡ W)
    → ap f p ∙ (ap f q ∙ r) ≡ ap f (p ∙ q) ∙ r
mpm f (refl _) q r = refl _

-- Rocq `mp_homot`: pull a path through homotopic maps.
mp-homot : {A : Type 𝓤} {B : Type 𝓥} (φ ψ : A → B)
           (hom : (a : A) → φ a ≡ ψ a) {x y : A} (p : x ≡ y)
         → ap φ p ≡ hom x ∙ ap ψ p ∙ (hom y) ⁻¹
mp-homot φ ψ hom (refl x) =
  (ap (λ z → z ∙ (hom x) ⁻¹) (right-unit (hom x)) ∙ right-inv (hom x)) ⁻¹

-- forward action of post/pre-comp-path-equiv (definitional up to right-unit).
postCompLem : {A : Type 𝓤} {x y z : A} (P : y ≡ z) (q : x ≡ y)
            → pr₁ (post-comp-path-equiv P) q ≡ q ∙ P
postCompLem (refl _) q = (right-unit q) ⁻¹

preCompLem : {A : Type 𝓤} {x y z : A} (P : x ≡ y) (q : y ≡ z)
           → pr₁ (pre-comp-path-equiv P) q ≡ P ∙ q
preCompLem (refl _) q = refl _

-- the product_map_eq commutation the s-part needs (Rocq `pme_square`).
pme-square : {A B Cc D : Cat}
  (t : Map A B) (l : Map A Cc) (r : Map B D) (b : Map Cc D)
  (s : comp r t ≡ comp b l)
  → (product-map-eq2 (comp b l) (comp-id-l (idMap 𝕀)) ∙ product-map-eq1 (idMap 𝕀) (s ⁻¹))
    ∙ (product-map-eq2 (comp r t) (comp-id-l (idMap 𝕀))) ⁻¹
  ≡ (product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) s) ⁻¹
pme-square t l r b s =
    ap (λ w → (x ∙ w) ∙ y ⁻¹) (product-map-eq1-inv (idMap 𝕀) s)
  ∙ (cancl a (((x ∙ z ⁻¹) ∙ y ⁻¹))) ⁻¹
  ∙ ap (λ w → a ⁻¹ ∙ w) reduce
  ∙ right-unit (a ⁻¹)
  where
  a = product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) s
  x = product-map-eq2 (comp b l) (comp-id-l (idMap 𝕀))
  y = product-map-eq2 (comp r t) (comp-id-l (idMap 𝕀))
  z = product-map-eq1 (idMap 𝕀) s
  C : a ∙ x ≡ y ∙ z
  C = product-map-eq-comm s (comp-id-l (idMap 𝕀))
  reduce : a ∙ ((x ∙ z ⁻¹) ∙ y ⁻¹) ≡ refl _
  reduce =
      solveR (ι a ⊕ ((ι x ⊕ ι (z ⁻¹)) ⊕ ι (y ⁻¹)))
             (((ι a ⊕ ι x) ⊕ ι (z ⁻¹)) ⊕ ι (y ⁻¹)) (refl _)
    ∙ ap (λ w → ((w ∙ z ⁻¹) ∙ y ⁻¹)) C
    ∙ solveR (((ι y ⊕ ι z) ⊕ ι (z ⁻¹)) ⊕ ι (y ⁻¹))
             (ι y ⊕ ((ι z ⊕ ι (z ⁻¹)) ⊕ ι (y ⁻¹))) (refl _)
    ∙ ap (λ w → y ∙ (w ∙ y ⁻¹)) (right-inv z)
    ∙ right-inv y

-- Rocq `key_pme`: the product-map coherence the s-part reduces to.
key-pme : {A B Cc D : Cat}
  (t : Map A B) (l : Map A Cc) (r : Map B D) (b : Map Cc D)
  (s : comp r t ≡ comp b l)
  (Pmclb : product-map (comp b l) (comp (idMap 𝕀) (idMap 𝕀))
         ≡ comp (product-map b (idMap 𝕀)) (product-map l (idMap 𝕀)))
  (Pmctr : product-map (comp r t) (comp (idMap 𝕀) (idMap 𝕀))
         ≡ comp (product-map r (idMap 𝕀)) (product-map t (idMap 𝕀)))
  → ((Pmclb ⁻¹ ∙ product-map-eq2 (comp b l) (comp-id-l (idMap 𝕀)))
       ∙ product-map-eq1 (idMap 𝕀) (s ⁻¹))
    ∙ (Pmctr ⁻¹ ∙ product-map-eq2 (comp r t) (comp-id-l (idMap 𝕀))) ⁻¹
  ≡ (Pmclb ⁻¹ ∙ (product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) s) ⁻¹) ∙ Pmctr
key-pme t l r b s Pmclb Pmctr =
    ap (λ w → ((Pmclb ⁻¹ ∙ x) ∙ product-map-eq1 (idMap 𝕀) (s ⁻¹)) ∙ w) step1
  ∙ solveR
      ((((ι (Pmclb ⁻¹) ⊕ ι x) ⊕ ι (product-map-eq1 (idMap 𝕀) (s ⁻¹)))
         ⊕ (ι (y ⁻¹) ⊕ ι Pmctr)))
      (ι (Pmclb ⁻¹) ⊕ ((((ι x ⊕ ι (product-map-eq1 (idMap 𝕀) (s ⁻¹))) ⊕ ι (y ⁻¹)) ⊕ ι Pmctr)))
      (refl _)
  ∙ ap (λ w → Pmclb ⁻¹ ∙ (w ∙ Pmctr)) (pme-square t l r b s)
  ∙ solveR (ι (Pmclb ⁻¹) ⊕ (ι (a ⁻¹) ⊕ ι Pmctr))
           ((ι (Pmclb ⁻¹) ⊕ ι (a ⁻¹)) ⊕ ι Pmctr)
           (refl _)
  where
  a = product-map-eq1 (comp (idMap 𝕀) (idMap 𝕀)) s
  x = product-map-eq2 (comp b l) (comp-id-l (idMap 𝕀))
  y = product-map-eq2 (comp r t) (comp-id-l (idMap 𝕀))
  step1 : (Pmctr ⁻¹ ∙ y) ⁻¹ ≡ y ⁻¹ ∙ Pmctr
  step1 = ∙-inv (Pmctr ⁻¹) y ∙ ap (λ w → y ⁻¹ ∙ w) (⁻¹⁻¹ Pmctr)

------------------------------------------------------------------------
-- §2  the isolated leaves (thin interface; Rocq `cone_reshuffle` /
--     `times_I_comparison_factor`).  `uncurry-precomp` above is exactly
--     the leaf coherence `cone-reshuffle`'s fibre map is built from.
------------------------------------------------------------------------

-- cone-reshuffle (Rocq `cone_reshuffle`):  a fibered equivalence built as
-- weqbandf = (fiberwise equiv) ; (change of base).  Base: uncurry on each
-- leg (product of exp-equivs).  Fibre over (g,e): `ap-equiv` of uncurry then
-- endpoint adjustment by `uncurry-precomp`.
--
-- It is `opaque`: its body is a huge equivalence term (nested
-- `invertible-to-equiv` contractibility data), and downstream forcing it
-- would blow up type-checking — only its TYPE is needed (cf. `product-map`
-- opacity).  baseEq / cone-fibEq are top-level so the opaque block is thin.
cone-baseEq : (S : Square) (X : Cat)
  → (Map (sqC S) (Fun 𝕀 X) × Map (sqB S) (Fun 𝕀 X))
  ≃ (Map (sqC S ×c 𝕀) X × Map (sqB S ×c 𝕀) X)
cone-baseEq S X = prod-equiv (exp-equiv 𝕀 X (sqC S)) (exp-equiv 𝕀 X (sqB S))

cone-fibEq : (S : Square) (X : Cat)
  (b1 : Map (sqC S) (Fun 𝕀 X) × Map (sqB S) (Fun 𝕀 X))
  → (comp (pr₁ b1) (sql S) ≡ comp (pr₂ b1) (sqt S))
  ≃ ( comp (pr₁ (exp-equiv 𝕀 X (sqC S)) (pr₁ b1)) (product-map (sql S) (idMap 𝕀))
    ≡ comp (pr₁ (exp-equiv 𝕀 X (sqB S)) (pr₂ b1)) (product-map (sqt S) (idMap 𝕀)) )
cone-fibEq S X (g , e) =
  equiv-comp (ap-equiv (exp-equiv 𝕀 X (sqA S)))
    (equiv-comp
      (post-comp-path-equiv (uncurry-precomp (sqt S) e))
      (pre-comp-path-equiv ((uncurry-precomp (sql S) g) ⁻¹)))

opaque
  cone-reshuffle : (S : Square) (X : Cat)
                 → sq-cone S (Fun 𝕀 X) ≃ sq-cone (times-I S) X
  cone-reshuffle S X =
    equiv-comp (Σ-fiberwise-equiv (cone-fibEq S X)) (Σ-change-of-base (cone-baseEq S X))

-- the forward fibre action of cone-fibEq, unfolded (Rocq's `cone_comm_reshuffle` RHS).
fibEq-expand : (S : Square) (X : Cat)
  (g : Map (sqC S) (Fun 𝕀 X)) (e : Map (sqB S) (Fun 𝕀 X))
  (p : comp g (sql S) ≡ comp e (sqt S))
  → pr₁ (cone-fibEq S X (g , e)) p
  ≡ (uncurry-precomp (sql S) g) ⁻¹
    ∙ (ap (exp-comparison 𝕀 X (sqA S)) p ∙ uncurry-precomp (sqt S) e)
fibEq-expand S X g e p =
    preCompLem ((uncurry-precomp (sql S) g) ⁻¹)
      (pr₁ (post-comp-path-equiv (uncurry-precomp (sqt S) e))
           (ap (exp-comparison 𝕀 X (sqA S)) p))
  ∙ ap (λ w → (uncurry-precomp (sql S) g) ⁻¹ ∙ w)
       (postCompLem (uncurry-precomp (sqt S) e) (ap (exp-comparison 𝕀 X (sqA S)) p))

-- LHS of uncurry-composeA reduced to ev∘product form via the bridge + prod-pent-C.
uncurry-composeA-lhs : {C0 C1 C2 X : Cat}
  (k : Map C2 (Fun 𝕀 X)) (g : Map C1 C2) (h : Map C0 C1)
  → ap (exp-comparison 𝕀 X C0) (composeA k g h)
  ≡ uncurry-bridge (comp (comp k g) h)
    ∙ (ap (comp (ev 𝕀 X)) (prodpent-rhs-C k g h)
       ∙ (uncurry-bridge (comp k (comp g h))) ⁻¹)
uncurry-composeA-lhs {C0} {C1} {C2} {X} k g h =
    mp-homot (exp-comparison 𝕀 X C0)
             (λ u → comp (ev 𝕀 X) (product-map u (idMap 𝕀)))
             uncurry-bridge (composeA k g h)
  ∙ ap (λ w → (uncurry-bridge (comp (comp k g) h) ∙ w)
              ∙ (uncurry-bridge (comp k (comp g h))) ⁻¹) midEq
  ∙ ∙-assoc (uncurry-bridge (comp (comp k g) h))
            (ap (comp (ev 𝕀 X)) (prodpent-rhs-C k g h))
            ((uncurry-bridge (comp k (comp g h))) ⁻¹)
  where
  midEq : ap (λ u → comp (ev 𝕀 X) (product-map u (idMap 𝕀))) (composeA k g h)
        ≡ ap (comp (ev 𝕀 X)) (prodpent-rhs-C k g h)
  midEq = (ap-comp (comp (ev 𝕀 X)) (λ u → product-map u (idMap 𝕀)) (composeA k g h)) ⁻¹
        ∙ ap (ap (comp (ev 𝕀 X))) (prod-pent-C k g h)

-- solve `a ∙ b ≡ c` for `a ≡ c ∙ b⁻¹`.
moveR : {A : Type 𝓤} {x y z : A} {a : x ≡ y} {b : y ≡ z} {c : x ≡ z}
      → a ∙ b ≡ c → a ≡ c ∙ b ⁻¹
moveR {a = a} {b} {c} H =
    (right-unit a) ⁻¹
  ∙ ap (λ w → a ∙ w) ((right-inv b) ⁻¹)
  ∙ (∙-assoc a b (b ⁻¹)) ⁻¹
  ∙ ap (λ w → w ∙ b ⁻¹) H

-- homotopy-naturality (Rocq `homotsec` / hnat): the workhorse for SLIDING the
-- bridge UBk : exp-comparison C2 k ≡ comp ev (product-map k Ic) through the
-- composeA/ccr cells of the target (a plain `ap` is ill-typed because the two
-- composeA's are not parallel — their endpoints differ along UBk).
hnat : {A : Type 𝓤} {B : Type 𝓥} (φ ψ : A → B) (H : (a : A) → φ a ≡ ψ a)
       {x y : A} (p : x ≡ y)
     → H x ∙ ap ψ p ≡ ap φ p ∙ H y
hnat φ ψ H (refl x) = right-unit (H x)

-- The two bridge-SLIDES for `uncurry-composeA` are proved below (these are the
-- only genuinely novel steps beyond the Rocq proof — they push the structural
-- bridge `UBk` through the composeA/ccr cells, producing bridge cells that cancel
-- the uncurry-precomp bridges pairwise).  `uncurry-composeA` then matches the
-- target to `uncurry-composeA-lhs`'s RHS by a cube-sized mechanical chain (see
-- the `times-I-factor` comment for the verified atom analysis).
uncurry-slide3 : {C0 C1 C2 X : Cat}
  (k : Map C2 (Fun 𝕀 X)) (g : Map C1 C2) (h : Map C0 C1)
  → composeA (exp-comparison 𝕀 X C2 k) (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))
  ≡ (ccl (product-map h (idMap 𝕀)) (ccl (product-map g (idMap 𝕀)) (uncurry-bridge k))
     ∙ composeA (comp (ev 𝕀 X) (product-map k (idMap 𝕀)))
         (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀)))
    ∙ (ccl (comp (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))) (uncurry-bridge k)) ⁻¹
uncurry-slide3 {C0} {C1} {C2} {X} k g h =
    moveR (hnat (λ f → comp (comp f (product-map g (idMap 𝕀))) (product-map h (idMap 𝕀)))
                (λ f → comp f (comp (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))))
                (λ f → composeA f (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀)))
                (uncurry-bridge k))
  ∙ ap (λ w → (w ∙ composeA (comp (ev 𝕀 X) (product-map k (idMap 𝕀)))
                    (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀)))
               ∙ (ccl (comp (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))) (uncurry-bridge k)) ⁻¹)
       ((ap-comp (λ w → comp w (product-map h (idMap 𝕀)))
                 (λ v → comp v (product-map g (idMap 𝕀))) (uncurry-bridge k)) ⁻¹)

uncurry-slide4 : {C0 C1 C2 X : Cat}
  (k : Map C2 (Fun 𝕀 X)) (g : Map C1 C2) (h : Map C0 C1)
  (W : comp (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀)) ≡ product-map (comp g h) (idMap 𝕀))
  → ccr (exp-comparison 𝕀 X C2 k) W
  ≡ (ccl (comp (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))) (uncurry-bridge k)
     ∙ ccr (comp (ev 𝕀 X) (product-map k (idMap 𝕀))) W)
    ∙ (ccl (product-map (comp g h) (idMap 𝕀)) (uncurry-bridge k)) ⁻¹
uncurry-slide4 {C0} {C1} {C2} {X} k g h W =
  moveR ((hnat (comp (exp-comparison 𝕀 X C2 k)) (comp (comp (ev 𝕀 X) (product-map k (idMap 𝕀))))
               (λ m → ccl m (uncurry-bridge k)) W) ⁻¹)

------------------------------------------------------------------------
-- §2b  uncurry-composeA  (Rocq `uncurry_composeA`, Main.v 6063):
--     the comparison's action on a `composeA` factors through the
--     uncurry-precomp/composeA(uncurry k)/pmc telescope.
------------------------------------------------------------------------

uncurry-composeA : {C0 C1 C2 X : Cat}
  (k : Map C2 (Fun 𝕀 X)) (g : Map C1 C2) (h : Map C0 C1)
  → ap (exp-comparison 𝕀 X C0) (composeA k g h)
  ≡ uncurry-precomp h (comp k g)
    ∙ ccl (product-map h (idMap 𝕀)) (uncurry-precomp g k)
    ∙ composeA (exp-comparison 𝕀 X C2 k) (product-map g (idMap 𝕀)) (product-map h (idMap 𝕀))
    ∙ ccr (exp-comparison 𝕀 X C2 k)
        ((pmc h g (idMap 𝕀) (idMap 𝕀)) ⁻¹ ∙ product-map-eq2 (comp g h) (comp-id-l (idMap 𝕀)))
    ∙ (uncurry-precomp (comp g h) k) ⁻¹
uncurry-composeA {C0} {C1} {C2} {X} k g h =
  uncurry-composeA-lhs k g h ∙ tgt-to-lhs ⁻¹
  where
  E = ev 𝕀 X
  Ic = idMap 𝕀
  pmk = product-map k Ic
  pmg = product-map g Ic
  pmh = product-map h Ic
  pmkg = product-map (comp k g) Ic
  pmgh = product-map (comp g h) Ic
  exp2 = exp-comparison 𝕀 X C2 k
  P = product-map-eq2 (comp k g) ((comp-id-l Ic) ⁻¹)
  Q = pmc g k Ic Ic
  Wt = (pmc h g Ic Ic) ⁻¹ ∙ product-map-eq2 (comp g h) (comp-id-l Ic)
  UBk = uncurry-bridge k
  UBkg = uncurry-bridge (comp k g)
  UBkgh = uncurry-bridge (comp (comp k g) h)
  UBkgh' = uncurry-bridge (comp k (comp g h))
  cp1 = product-map-eq2 (comp (comp k g) h) ((comp-id-l Ic) ⁻¹)
  cp2 = pmc h (comp k g) Ic Ic
  cp3 = ccl pmh (P ∙ Q)
  cp4 = composeA pmk pmg pmh
  cp5 = ccr pmk Wt
  cp6 = (pmc (comp g h) k Ic Ic) ⁻¹
  cp7 = (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹)) ⁻¹
  aE1 = ap (comp E) cp1
  aE2 = ap (comp E) cp2
  aE3 = ap (comp E) cp3
  aE4 = ap (comp E) cp4
  aE5 = ap (comp E) cp5
  aE6 = ap (comp E) cp6
  aE7 = ap (comp E) cp7
  -- 24 atoms in canonical order
  a1 = UBkgh
  a2 = aE1
  a3 = aE2
  a4 = (composeA E pmkg pmh) ⁻¹
  a5 = ccl pmh (UBkg ⁻¹)
  b1 = ccl pmh UBkg
  b2 = ccl pmh (ccr E P)
  b3 = ccl pmh (ccr E Q)
  b4 = ccl pmh ((composeA E pmk pmg) ⁻¹)
  b5 = ccl pmh (ccl pmg (UBk ⁻¹))
  c0 = ccl pmh (ccl pmg UBk)
  pent1 = ccl pmh (composeA E pmk pmg)
  pent2 = composeA E (comp pmk pmg) pmh
  pent3 = ccr E (composeA pmk pmg pmh)
  pent4 = (composeA E pmk (comp pmg pmh)) ⁻¹
  clast = (ccl (comp pmg pmh) UBk) ⁻¹
  d0 = ccl (comp pmg pmh) UBk
  d1 = ccr (comp E pmk) Wt
  dlast = (ccl pmgh UBk) ⁻¹
  e0 = ccl pmgh UBk
  e1 = composeA E pmk pmgh
  e2 = aE6
  e3 = aE7
  e4 = UBkgh' ⁻¹

  cclpmh-dist : ccl pmh (uncurry-precomp g k)
              ≡ b1 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (b5))))
  cclpmh-dist =
      ap-∙ (λ m → comp m pmh) (((UBkg ∙ ccr E P) ∙ ccr E Q) ∙ (composeA E pmk pmg) ⁻¹) (ccl pmg (UBk ⁻¹))
    ∙ ap (λ z → z ∙ b5) (ap-∙ (λ m → comp m pmh) ((UBkg ∙ ccr E P) ∙ ccr E Q) ((composeA E pmk pmg) ⁻¹))
    ∙ ap (λ z → (z ∙ b4) ∙ b5) (ap-∙ (λ m → comp m pmh) (UBkg ∙ ccr E P) (ccr E Q))
    ∙ ap (λ z → ((z ∙ b3) ∙ b4) ∙ b5) (ap-∙ (λ m → comp m pmh) UBkg (ccr E P))
    ∙ solveR ((((ι b1 ⊕ ι b2) ⊕ ι b3) ⊕ ι b4) ⊕ ι b5)
             ((ι b1 ⊕ (ι b2 ⊕ (ι b3 ⊕ (ι b4 ⊕ (ι b5))))))
             (refl _)

  eqT3 : composeA exp2 pmg pmh ≡ c0 ∙ (pent1 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast)))))
  eqT3 =
      uncurry-slide3 k g h
    ∙ ap (λ z → (c0 ∙ z) ∙ clast) (pentL E pmk pmg pmh)
    ∙ solveR ((ι c0 ⊕ (((ι pent1 ⊕ ι pent2) ⊕ ι pent3) ⊕ ι pent4)) ⊕ ι clast)
             ((ι c0 ⊕ (ι pent1 ⊕ (ι pent2 ⊕ (ι pent3 ⊕ (ι pent4 ⊕ (ι clast)))))))
             (refl _)

  eqT4 : ccr exp2 Wt ≡ d0 ∙ (d1 ∙ (dlast))
  eqT4 =
      uncurry-slide4 k g h Wt
    ∙ solveR ((ι d0 ⊕ ι d1) ⊕ ι dlast) ((ι d0 ⊕ (ι d1 ⊕ (ι dlast)))) (refl _)

  t5-inv : (uncurry-precomp (comp g h) k) ⁻¹ ≡ e0 ∙ (e1 ∙ (e2 ∙ (e3 ∙ (e4))))
  t5-inv =
      ∙-inv (((UBkgh' ∙ ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ∙ ccr E (pmc (comp g h) k Ic Ic)) ∙ (composeA E pmk pmgh) ⁻¹) (ccl pmgh (UBk ⁻¹))
    ∙ ap (λ z → (ccl pmgh (UBk ⁻¹)) ⁻¹ ∙ z) (∙-inv ((UBkgh' ∙ ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ∙ ccr E (pmc (comp g h) k Ic Ic)) ((composeA E pmk pmgh) ⁻¹))
    ∙ ap (λ z → (ccl pmgh (UBk ⁻¹)) ⁻¹ ∙ ((composeA E pmk pmgh) ⁻¹ ⁻¹ ∙ z)) (∙-inv (UBkgh' ∙ ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) (ccr E (pmc (comp g h) k Ic Ic)))
    ∙ ap (λ z → (ccl pmgh (UBk ⁻¹)) ⁻¹ ∙ ((composeA E pmk pmgh) ⁻¹ ⁻¹ ∙ ((ccr E (pmc (comp g h) k Ic Ic)) ⁻¹ ∙ z))) (∙-inv UBkgh' (ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))))
    ∙ ap (λ z → z ∙ ((composeA E pmk pmgh) ⁻¹ ⁻¹ ∙ ((ccr E (pmc (comp g h) k Ic Ic)) ⁻¹ ∙ ((ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ⁻¹ ∙ UBkgh' ⁻¹)))) w5inv
    ∙ ap (λ z → e0 ∙ (z ∙ ((ccr E (pmc (comp g h) k Ic Ic)) ⁻¹ ∙ ((ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ⁻¹ ∙ UBkgh' ⁻¹)))) (⁻¹⁻¹ (composeA E pmk pmgh))
    ∙ ap (λ z → e0 ∙ (e1 ∙ (z ∙ ((ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ⁻¹ ∙ UBkgh' ⁻¹)))) w3inv
    ∙ ap (λ z → e0 ∙ (e1 ∙ (e2 ∙ (z ∙ UBkgh' ⁻¹)))) w2inv
    where
    w5inv : (ccl pmgh (UBk ⁻¹)) ⁻¹ ≡ e0
    w5inv = ap _⁻¹ (ap-⁻¹ (λ m → comp m pmgh) UBk) ∙ ⁻¹⁻¹ (ccl pmgh UBk)
    w3inv : (ccr E (pmc (comp g h) k Ic Ic)) ⁻¹ ≡ e2
    w3inv = (ap-⁻¹ (comp E) (pmc (comp g h) k Ic Ic)) ⁻¹
    w2inv : (ccr E (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ⁻¹ ≡ e3
    w2inv = (ap-⁻¹ (comp E) (product-map-eq2 (comp k (comp g h)) ((comp-id-l Ic) ⁻¹))) ⁻¹

  distrib : ap (comp E) (prodpent-rhs-C k g h)
          ≡ aE1 ∙ (aE2 ∙ (aE3 ∙ (aE4 ∙ (aE5 ∙ (aE6 ∙ aE7)))))
  distrib =
      ap-∙ (comp E) cp1 (cp2 ∙ (cp3 ∙ (cp4 ∙ (cp5 ∙ (cp6 ∙ cp7)))))
    ∙ ap (λ z → aE1 ∙ z)
        ( ap-∙ (comp E) cp2 (cp3 ∙ (cp4 ∙ (cp5 ∙ (cp6 ∙ cp7))))
        ∙ ap (λ z → aE2 ∙ z)
            ( ap-∙ (comp E) cp3 (cp4 ∙ (cp5 ∙ (cp6 ∙ cp7)))
            ∙ ap (λ z → aE3 ∙ z)
                ( ap-∙ (comp E) cp4 (cp5 ∙ (cp6 ∙ cp7))
                ∙ ap (λ z → aE4 ∙ z)
                    ( ap-∙ (comp E) cp5 (cp6 ∙ cp7)
                    ∙ ap (λ z → aE5 ∙ z) (ap-∙ (comp E) cp6 cp7)))))

  core-eq : {W : Map (C0 ×c 𝕀) X} (rest : comp E (comp pmk pmgh) ≡ W)
          → (composeA E pmkg pmh) ⁻¹
            ∙ (ccl pmh (ccr E P) ∙ (ccl pmh (ccr E Q) ∙ (composeA E (comp pmk pmg) pmh
            ∙ (ccr E (composeA pmk pmg pmh) ∙ ((composeA E pmk (comp pmg pmh)) ⁻¹
            ∙ (ccr (comp E pmk) Wt ∙ (composeA E pmk pmgh ∙ rest)))))))
          ≡ aE3 ∙ (aE4 ∙ (aE5 ∙ rest))
  core-eq rest =
      slideA E pmh P Q rest1
    ∙ ap (λ z → z ∙ rest1) ((ap-comp (comp E) (λ w → comp w pmh) (P ∙ Q)) ⁻¹)
    ∙ ap (λ z → aE3 ∙ (aE4 ∙ z))
         (slideB E pmk Wt rest
          ∙ ap (λ z → z ∙ rest) ((ap-comp (comp E) (comp pmk) Wt) ⁻¹))
    where
    rest1 = ccr E (composeA pmk pmg pmh)
            ∙ ((composeA E pmk (comp pmg pmh)) ⁻¹
            ∙ (ccr (comp E pmk) Wt ∙ (composeA E pmk pmgh ∙ rest)))

  tgt-to-lhs :
      uncurry-precomp h (comp k g)
      ∙ ccl pmh (uncurry-precomp g k)
      ∙ composeA exp2 pmg pmh
      ∙ ccr exp2 Wt
      ∙ (uncurry-precomp (comp g h) k) ⁻¹
    ≡ UBkgh ∙ (ap (comp E) (prodpent-rhs-C k g h) ∙ UBkgh' ⁻¹)
  tgt-to-lhs =
      ap (λ z → uncurry-precomp h (comp k g) ∙ z ∙ composeA exp2 pmg pmh ∙ ccr exp2 Wt ∙ (uncurry-precomp (comp g h) k) ⁻¹) cclpmh-dist
    ∙ ap (λ z → uncurry-precomp h (comp k g) ∙ (b1 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (b5))))) ∙ z ∙ ccr exp2 Wt ∙ (uncurry-precomp (comp g h) k) ⁻¹) eqT3
    ∙ ap (λ z → uncurry-precomp h (comp k g) ∙ (b1 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (b5))))) ∙ (c0 ∙ (pent1 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast)))))) ∙ z ∙ (uncurry-precomp (comp g h) k) ⁻¹) eqT4
    ∙ ap (λ z → uncurry-precomp h (comp k g) ∙ (b1 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (b5))))) ∙ (c0 ∙ (pent1 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast)))))) ∙ (d0 ∙ (d1 ∙ (dlast))) ∙ z) t5-inv
    ∙ solveR ((((((((ι a1 ⊕ ι a2) ⊕ ι a3) ⊕ ι a4) ⊕ ι a5) ⊕ ((ι b1 ⊕ (ι b2 ⊕ (ι b3 ⊕ (ι b4 ⊕ (ι b5))))))) ⊕ ((ι c0 ⊕ (ι pent1 ⊕ (ι pent2 ⊕ (ι pent3 ⊕ (ι pent4 ⊕ (ι clast)))))))) ⊕ ((ι d0 ⊕ (ι d1 ⊕ (ι dlast))))) ⊕ (ι e0 ⊕ (ι e1 ⊕ (ι e2 ⊕ (ι e3 ⊕ (ι e4)))))) (ι a1 ⊕ (ι a2 ⊕ (ι a3 ⊕ (ι a4 ⊕ (ι a5 ⊕ (ι b1 ⊕ (ι b2 ⊕ (ι b3 ⊕ (ι b4 ⊕ (ι b5 ⊕ (ι c0 ⊕ (ι pent1 ⊕ (ι pent2 ⊕ (ι pent3 ⊕ (ι pent4 ⊕ (ι clast ⊕ (ι d0 ⊕ (ι d1 ⊕ (ι dlast ⊕ (ι e0 ⊕ (ι e1 ⊕ (ι e2 ⊕ (ι e3 ⊕ (ι e4)))))))))))))))))))))))) (refl _)
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ (a4 ∙ (z))))) (cancl-ap (λ m → comp m pmh) UBkg (b2 ∙ (b3 ∙ (b4 ∙ (b5 ∙ (c0 ∙ (pent1 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast ∙ (d0 ∙ (d1 ∙ (dlast ∙ (e0 ∙ (e1 ∙ (e2 ∙ (e3 ∙ (e4)))))))))))))))))))
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ (a4 ∙ (b2 ∙ (b3 ∙ (b4 ∙ (z)))))))) (cancl-ccl2 pmh pmg UBk (pent1 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast ∙ (d0 ∙ (d1 ∙ (dlast ∙ (e0 ∙ (e1 ∙ (e2 ∙ (e3 ∙ (e4))))))))))))))
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ (a4 ∙ (b2 ∙ (b3 ∙ (z))))))) (cancl-ap (λ m → comp m pmh) (composeA E pmk pmg) (pent2 ∙ (pent3 ∙ (pent4 ∙ (clast ∙ (d0 ∙ (d1 ∙ (dlast ∙ (e0 ∙ (e1 ∙ (e2 ∙ (e3 ∙ (e4)))))))))))))
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ (a4 ∙ (b2 ∙ (b3 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (z)))))))))) (cancl (ccl (comp pmg pmh) UBk) (d1 ∙ (dlast ∙ (e0 ∙ (e1 ∙ (e2 ∙ (e3 ∙ (e4))))))))
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ (a4 ∙ (b2 ∙ (b3 ∙ (pent2 ∙ (pent3 ∙ (pent4 ∙ (d1 ∙ (z))))))))))) (cancl (ccl pmgh UBk) (e1 ∙ (e2 ∙ (e3 ∙ (e4)))))
    ∙ ap (λ z → a1 ∙ (a2 ∙ (a3 ∙ z))) (core-eq (e2 ∙ (e3 ∙ e4)))
    ∙ ap (λ z → UBkgh ∙ z)
         (solveR ((ι aE1 ⊕ (ι aE2 ⊕ (ι aE3 ⊕ (ι aE4 ⊕ (ι aE5 ⊕ (ι aE6 ⊕ (ι aE7 ⊕ ι (UBkgh' ⁻¹))))))))) ((ι aE1 ⊕ (ι aE2 ⊕ (ι aE3 ⊕ (ι aE4 ⊕ (ι aE5 ⊕ (ι aE6 ⊕ ι aE7)))))) ⊕ ι (UBkgh' ⁻¹)) (refl _)
          ∙ ap (λ z → z ∙ UBkgh' ⁻¹) (distrib ⁻¹))

-- Compute the cone-reshuffle forward action on a cone (the ONLY place that
-- unfolds cone-reshuffle).  Definitionally the forward maps reduce on the
-- explicit pair, so this is `refl`; isolating it keeps every downstream proof
-- free of the huge equivalence term.
opaque
  unfolding cone-reshuffle
  reshuffle-fwd-eq : (S : Square) (X : Cat) (c : sq-cone S (Fun 𝕀 X))
    → pr₁ (cone-reshuffle S X) c
    ≡ ( ( pr₁ (exp-equiv 𝕀 X (sqC S)) (cg S (Fun 𝕀 X) c)
        , pr₁ (exp-equiv 𝕀 X (sqB S)) (ce S (Fun 𝕀 X) c) )
      , pr₁ (cone-fibEq S X (pr₁ c)) (cc S (Fun 𝕀 X) c) )
  reshuffle-fwd-eq S X c = refl _

-- Rocq `abstract_helper` (Main.v 6213): the comparison for T×𝕀 at the
-- uncurried map equals the cone-reshuffle of the comparison for T over Fun 𝕀 X.
abstract-helper : (S : Square) (X : Cat) (k : Map (sqD S) (Fun 𝕀 X))
  → sq-comparison (times-I S) X (exp-comparison 𝕀 X (sqD S) k)
  ≡ pr₁ (cone-reshuffle S X) (sq-comparison S (Fun 𝕀 X) k)
abstract-helper S X k =
    cone-eq {times-I S} {X} {cL} {EC} pg pe coh
  ∙ (reshuffle-fwd-eq S X (sq-comparison S (Fun 𝕀 X) k)) ⁻¹
  where
  A   = sqA S
  Bc  = sqB S
  Cc  = sqC S
  Dd  = sqD S
  t   = sqt S
  l   = sql S
  r   = sqr S
  bb  = sqb S
  s   = sqcomm S
  Ic  = idMap 𝕀
  uk  = exp-comparison 𝕀 X Dd k
  ccA = exp-comparison 𝕀 X A
  pmb = product-map bb Ic
  pml = product-map l Ic
  pmr = product-map r Ic
  pmt = product-map t Ic
  cL  = sq-comparison (times-I S) X uk
  commK = composeA k bb l ∙ ap (comp k) (s ⁻¹) ∙ (composeA k r t) ⁻¹
  EC : sq-cone (times-I S) X
  EC = ( (exp-comparison 𝕀 X Cc (comp k bb) , exp-comparison 𝕀 X Bc (comp k r))
       , pr₁ (cone-fibEq S X (comp k bb , comp k r)) commK )
  Ubk = uncurry-precomp bb k
  Urk = uncurry-precomp r k
  Ulkb = uncurry-precomp l (comp k bb)
  Utkr = uncurry-precomp t (comp k r)
  Ubl = uncurry-precomp (comp bb l) k
  Urt = uncurry-precomp (comp r t) k
  PLb = ccl pml Ubk
  PRt = ccl pmt Urk
  Wbl = (pmc l bb Ic Ic) ⁻¹ ∙ product-map-eq2 (comp bb l) (comp-id-l Ic)
  Wrt = (pmc t r Ic Ic) ⁻¹ ∙ product-map-eq2 (comp r t) (comp-id-l Ic)
  X1  = composeA uk pmb pml
  X2  = ccr uk Wbl
  X4' = composeA uk pmr pmt
  X5' = ccr uk Wrt
  MIDψ = ap (λ k0 → comp uk (product-map k0 Ic)) (s ⁻¹)
  T   = ap (comp uk) ((times-I-comm S) ⁻¹)
  pme1s = product-map-eq1 (comp Ic Ic) s

  pg : comp uk pmb ≡ exp-comparison 𝕀 X Cc (comp k bb)
  pg = (uncurry-precomp bb k) ⁻¹
  pe : comp uk pmr ≡ exp-comparison 𝕀 X Bc (comp k r)
  pe = (uncurry-precomp r k) ⁻¹

  h1 = PLb ⁻¹
  h2 = Ulkb ⁻¹
  h3 = Ulkb
  h4 = PLb
  h5 = X1
  h6 = X2
  h7 = Ubl ⁻¹
  h8 = Ubl
  h9 = MIDψ
  h10 = Urt ⁻¹
  h11 = Urt
  h12 = X5' ⁻¹
  h13 = X4' ⁻¹
  h14 = PRt ⁻¹
  h15 = Utkr ⁻¹
  h16 = Utkr

  pg-eq : ccl pml pg ≡ PLb ⁻¹
  pg-eq = ap-⁻¹ (λ m → comp m pml) Ubk

  eqTELbl : ap ccA (composeA k bb l) ≡ Ulkb ∙ (PLb ∙ (X1 ∙ (X2 ∙ Ubl ⁻¹)))
  eqTELbl = uncurry-composeA k bb l
    ∙ solveR ((((ι Ulkb ⊕ ι PLb) ⊕ ι X1) ⊕ ι X2) ⊕ ι (Ubl ⁻¹))
             (ι Ulkb ⊕ (ι PLb ⊕ (ι X1 ⊕ (ι X2 ⊕ ι (Ubl ⁻¹))))) (refl _)

  eqTELrt : ap ccA (composeA k r t) ≡ Utkr ∙ (PRt ∙ (X4' ∙ (X5' ∙ Urt ⁻¹)))
  eqTELrt = uncurry-composeA k r t
    ∙ solveR ((((ι Utkr ⊕ ι PRt) ⊕ ι X4') ⊕ ι X5') ⊕ ι (Urt ⁻¹))
             (ι Utkr ⊕ (ι PRt ⊕ (ι X4' ⊕ (ι X5' ⊕ ι (Urt ⁻¹))))) (refl _)

  MID-eq : ap ccA (ap (comp k) (s ⁻¹)) ≡ Ubl ∙ (MIDψ ∙ Urt ⁻¹)
  MID-eq = ap-comp ccA (comp k) (s ⁻¹)
    ∙ mp-homot (λ k0 → exp-comparison 𝕀 X A (comp k k0))
               (λ k0 → comp uk (product-map k0 Ic))
               (λ k0 → uncurry-precomp k0 k) (s ⁻¹)
    ∙ solveR ((ι Ubl ⊕ ι MIDψ) ⊕ ι (Urt ⁻¹)) (ι Ubl ⊕ (ι MIDψ ⊕ ι (Urt ⁻¹))) (refl _)

  eqTELrtInv : (Utkr ∙ (PRt ∙ (X4' ∙ (X5' ∙ Urt ⁻¹)))) ⁻¹
             ≡ Urt ∙ (X5' ⁻¹ ∙ (X4' ⁻¹ ∙ (PRt ⁻¹ ∙ Utkr ⁻¹)))
  eqTELrtInv =
      ∙-inv Utkr (PRt ∙ (X4' ∙ (X5' ∙ Urt ⁻¹)))
    ∙ ap (λ z → z ∙ Utkr ⁻¹) (∙-inv PRt (X4' ∙ (X5' ∙ Urt ⁻¹)))
    ∙ ap (λ z → (z ∙ PRt ⁻¹) ∙ Utkr ⁻¹) (∙-inv X4' (X5' ∙ Urt ⁻¹))
    ∙ ap (λ z → ((z ∙ X4' ⁻¹) ∙ PRt ⁻¹) ∙ Utkr ⁻¹) (∙-inv X5' (Urt ⁻¹))
    ∙ ap (λ z → (((z ∙ X5' ⁻¹) ∙ X4' ⁻¹) ∙ PRt ⁻¹) ∙ Utkr ⁻¹) (⁻¹⁻¹ Urt)
    ∙ solveR ((((ι Urt ⊕ ι (X5' ⁻¹)) ⊕ ι (X4' ⁻¹)) ⊕ ι (PRt ⁻¹)) ⊕ ι (Utkr ⁻¹))
             (ι Urt ⊕ (ι (X5' ⁻¹) ⊕ (ι (X4' ⁻¹) ⊕ (ι (PRt ⁻¹) ⊕ ι (Utkr ⁻¹))))) (refl _)

  apccA-full : ap ccA commK
    ≡ ((Ulkb ∙ (PLb ∙ (X1 ∙ (X2 ∙ Ubl ⁻¹)))) ∙ (Ubl ∙ (MIDψ ∙ Urt ⁻¹)))
      ∙ (Urt ∙ (X5' ⁻¹ ∙ (X4' ⁻¹ ∙ (PRt ⁻¹ ∙ Utkr ⁻¹))))
  apccA-full =
      ap-∙ ccA (composeA k bb l ∙ ap (comp k) (s ⁻¹)) ((composeA k r t) ⁻¹)
    ∙ ap (λ z → z ∙ ap ccA ((composeA k r t) ⁻¹))
         (ap-∙ ccA (composeA k bb l) (ap (comp k) (s ⁻¹)))
    ∙ ap (λ z → (z ∙ ap ccA (ap (comp k) (s ⁻¹))) ∙ ap ccA ((composeA k r t) ⁻¹)) eqTELbl
    ∙ ap (λ z → ((Ulkb ∙ (PLb ∙ (X1 ∙ (X2 ∙ Ubl ⁻¹)))) ∙ z) ∙ ap ccA ((composeA k r t) ⁻¹)) MID-eq
    ∙ ap (λ z → ((Ulkb ∙ (PLb ∙ (X1 ∙ (X2 ∙ Ubl ⁻¹)))) ∙ (Ubl ∙ (MIDψ ∙ Urt ⁻¹))) ∙ z)
         (ap-⁻¹ ccA (composeA k r t) ∙ ap _⁻¹ eqTELrt ∙ eqTELrtInv)

  midcoh : X2 ∙ (MIDψ ∙ X5' ⁻¹) ≡ T
  midcoh =
      ap (λ z → X2 ∙ (z ∙ X5' ⁻¹)) ((ap-comp (comp uk) (λ f → product-map f Ic) (s ⁻¹)) ⁻¹)
    ∙ ap (λ z → X2 ∙ (ap (comp uk) pme1s' ∙ z)) ((ap-⁻¹ (comp uk) Wrt) ⁻¹)
    ∙ ap (λ z → X2 ∙ z) ((ap-∙ (comp uk) pme1s' (Wrt ⁻¹)) ⁻¹)
    ∙ (ap-∙ (comp uk) Wbl (pme1s' ∙ Wrt ⁻¹)) ⁻¹
    ∙ ap (ap (comp uk))
         ( solveR (ι Wbl ⊕ (ι pme1s' ⊕ ι (Wrt ⁻¹))) ((ι Wbl ⊕ ι pme1s') ⊕ ι (Wrt ⁻¹)) (refl _)
         ∙ key-pme t l r bb s (pmc l bb Ic Ic) (pmc t r Ic Ic)
         ∙ tIcomm-inv )
    where
    pme1s' = product-map-eq1 Ic (s ⁻¹)
    tIcomm-inv : ((pmc l bb Ic Ic) ⁻¹ ∙ pme1s ⁻¹) ∙ pmc t r Ic Ic ≡ (times-I-comm S) ⁻¹
    tIcomm-inv =
        solveR ((ι ((pmc l bb Ic Ic) ⁻¹) ⊕ ι (pme1s ⁻¹)) ⊕ ι (pmc t r Ic Ic))
               (ι ((pmc l bb Ic Ic) ⁻¹) ⊕ (ι (pme1s ⁻¹) ⊕ ι (pmc t r Ic Ic))) (refl _)
      ∙ ap (λ z → (pmc l bb Ic Ic) ⁻¹ ∙ (pme1s ⁻¹ ∙ z)) ((⁻¹⁻¹ (pmc t r Ic Ic)) ⁻¹)
      ∙ ap (λ z → (pmc l bb Ic Ic) ⁻¹ ∙ z) ((∙-inv ((pmc t r Ic Ic) ⁻¹) pme1s) ⁻¹)
      ∙ (∙-inv ((pmc t r Ic Ic) ⁻¹ ∙ pme1s) (pmc l bb Ic Ic)) ⁻¹

  PRt-conv : PRt ⁻¹ ≡ ccl pmt pe
  PRt-conv = (ap-⁻¹ (λ m → comp m pmt) Urk) ⁻¹

  coh : ccl pml pg ∙ cc (times-I S) X EC ≡ cc (times-I S) X cL ∙ ccl pmt pe
  coh =
      ap (λ z → z ∙ cc (times-I S) X EC) pg-eq
    ∙ ap (λ z → PLb ⁻¹ ∙ z) (fibEq-expand S X (comp k bb) (comp k r) commK)
    ∙ ap (λ z → PLb ⁻¹ ∙ (Ulkb ⁻¹ ∙ (z ∙ Utkr))) apccA-full
    ∙ solveR (ι h1 ⊕ (ι h2 ⊕ ((( (ι h3 ⊕ (ι h4 ⊕ (ι h5 ⊕ (ι h6 ⊕ ι h7)))) ⊕ (ι h8 ⊕ (ι h9 ⊕ ι h10)) ) ⊕ (ι h11 ⊕ (ι h12 ⊕ (ι h13 ⊕ (ι h14 ⊕ ι h15)))) ) ⊕ ι h16))) (ι h1 ⊕ (ι h2 ⊕ (ι h3 ⊕ (ι h4 ⊕ (ι h5 ⊕ (ι h6 ⊕ (ι h7 ⊕ (ι h8 ⊕ (ι h9 ⊕ (ι h10 ⊕ (ι h11 ⊕ (ι h12 ⊕ (ι h13 ⊕ (ι h14 ⊕ (ι h15 ⊕ ι h16))))))))))))))) (refl _)
    ∙ ap (λ z → h1 ∙ z) (cancl Ulkb (h4 ∙ (h5 ∙ (h6 ∙ (h7 ∙ (h8 ∙ (h9 ∙ (h10 ∙ (h11 ∙ (h12 ∙ (h13 ∙ (h14 ∙ (h15 ∙ h16)))))))))))))
    ∙ cancl PLb (h5 ∙ (h6 ∙ (h7 ∙ (h8 ∙ (h9 ∙ (h10 ∙ (h11 ∙ (h12 ∙ (h13 ∙ (h14 ∙ (h15 ∙ h16)))))))))))
    ∙ ap (λ z → h5 ∙ (h6 ∙ z)) (cancl Ubl (h9 ∙ (h10 ∙ (h11 ∙ (h12 ∙ (h13 ∙ (h14 ∙ (h15 ∙ h16))))))))
    ∙ ap (λ z → h5 ∙ (h6 ∙ (h9 ∙ z))) (cancl Urt (h12 ∙ (h13 ∙ (h14 ∙ (h15 ∙ h16)))))
    ∙ ap (λ z → h5 ∙ (h6 ∙ (h9 ∙ (h12 ∙ (h13 ∙ z)))))
         (ap (λ z → PRt ⁻¹ ∙ z) (left-inv Utkr) ∙ right-unit (PRt ⁻¹))
    ∙ ap (λ z → X1 ∙ (X2 ∙ (MIDψ ∙ (X5' ⁻¹ ∙ (X4' ⁻¹ ∙ z))))) PRt-conv
    ∙ solveR (ι X1 ⊕ (ι X2 ⊕ (ι MIDψ ⊕ (ι (X5' ⁻¹) ⊕ (ι (X4' ⁻¹) ⊕ ι (ccl pmt pe))))))
             (ι X1 ⊕ ((ι X2 ⊕ (ι MIDψ ⊕ ι (X5' ⁻¹))) ⊕ (ι (X4' ⁻¹) ⊕ ι (ccl pmt pe)))) (refl _)
    ∙ ap (λ z → X1 ∙ (z ∙ (X4' ⁻¹ ∙ ccl pmt pe))) midcoh
    ∙ solveR (ι X1 ⊕ (ι T ⊕ (ι (X4' ⁻¹) ⊕ ι (ccl pmt pe))))
             (((ι X1 ⊕ ι T) ⊕ ι (X4' ⁻¹)) ⊕ ι (ccl pmt pe)) (refl _)

-- Rocq `times_I_comparison_factor` (Main.v 6266): h = uncurry (curry h),
-- so the comparison for T×𝕀 factors through cone-reshuffle.
times-I-factor : (S : Square) (X : Cat) (h : Map (sqD S ×c 𝕀) X)
  → sq-comparison (times-I S) X h
  ≡ pr₁ (cone-reshuffle S X)
      (sq-comparison S (Fun 𝕀 X) (equiv-inv (exp-equiv 𝕀 X (sqD S)) h))
times-I-factor S X h =
    ap (sq-comparison (times-I S) X) (equiv-inv-rinv (exp-equiv 𝕀 X (sqD S)) h) ⁻¹
  ∙ abstract-helper S X (equiv-inv (exp-equiv 𝕀 X (sqD S)) h)

-----
-- §3  − ×c 𝕀 preserves pushouts: the comparison for T×𝕀 is homotopic to
--     the composite  (curry) ; (comparison at Fun 𝕀 X) ; (cone-reshuffle),
--     a composite of three equivalences.
------------------------------------------------------------------------

times-I-preserves : {S : Square} → is-pushout-square S → is-pushout-square (times-I S)
times-I-preserves {S} H X =
  equiv-from-homotopy
    (sq-comparison (times-I S) X)
    (pr₁ comp-equiv)
    (times-I-factor S X)
    (pr₂ comp-equiv)
  where
  comp-equiv : Map (sqD S ×c 𝕀) X ≃ sq-cone (times-I S) X
  comp-equiv =
    equiv-comp
      (equiv-comp (inv-equiv (exp-equiv 𝕀 X (sqD S)))
                  (sq-comparison S (Fun 𝕀 X) , H (Fun 𝕀 X)))
      (cone-reshuffle S X)
