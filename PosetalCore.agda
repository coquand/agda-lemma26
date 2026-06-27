{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26 — SHARED interface (Stream A ⇄ Stream B contract).
--
-- Posetality of categories (Rocq `is_posetal`, HANDOFF §1).  `is-posetal`
-- is the agreed definition (here strengthened with clause (3), `is-set (Ob C)`,
-- matching Rocq's separate `isaset (Ob C)` hypothesis — see the note on the
-- definition below).  Stream A's four deliverables are PROVED here:
--   posetal-eq-objects, posetal-hom-is-set, I-posetal  (postulate-free)
--   Delta-posetal                                       (base + induction
--       proved; rests on the single isolated `Fun-posetal`, the nerve
--       universal property — see its postulate for what remains).
--
-- NB there is NO global `map-is-set` (the codebase is `map-is-set`-free), so
-- `posetal-hom-is-set` is the genuine source of Stream B's `is-set` hypotheses.
------------------------------------------------------------------------

module PosetalCore where

open import Spartan
open import CatAxioms
open import HigherCat using (𝕀; 𝕀-ob; 𝟚; Mor; equiv-inj;
  map-between-contrs-is-equiv)
open import Constructions using (Hom; Hom-map; dom; cod; id-mor; dom-id; cod-id;
  𝕀₀; 𝕀₁; dom-nat; cod-nat; funct-on-mor; equiv-inv)
open import Pullbacks using (_×c_; π₁; π₂; ⟨_,_⟩; pair-β₁; pair-β₂; pair-η;
  equiv-inv-rinv; equiv-inv-linv)
open import Exponentials using (Fun; ev; exp-comparison; exp-equiv;
  ob-to-map; map-to-ob; ob-map-roundtrip₁; ob-map-roundtrip₂)
open import Interval using (Δ; ob-to-𝟚; 𝕀-char; 𝕀-char-comparison;
  𝕀-char-inverse; 𝕀-char-rinv; 𝕀-char-linv; is-monotone; is-monotone-is-prop;
  invertible-to-equiv; ob-map-equiv; Monotone; equiv-comp; pair-nat; pair-ap;
  _≤𝟚_; ≤𝟚-trans; ≤𝟚-transport; 𝕀-mor-order; mor-to-pointwise;
  pointwise-to-mor; 𝕀-char-ob-to-𝟚; Hom-coerce)
open import HLevels using (hedberg-set; ob-𝕀-is-set; ×-is-prop;
  fn-into-contr-is-contr; Σ-prop-contr; equiv-is-set; fn-into-set;
  Σ-set-prop; 𝟚-is-set)
open import IntervalPosetal using (𝕀-thin; 𝕀-hom-to-order; map-into-𝕀-eq; val-𝕀;
  𝕀-order-to-hom)
open import FaceOrdCompat using (ev-point)

-- a function on objects is monotone if it preserves the (thin) hom-relation.
is-monotone-ob : {D C : Cat} → (Ob D → Ob C) → Type 𝓤₀
is-monotone-ob {D} {C} f = (x y : Ob D) → Hom D x y → Hom C (f x) (f y)

-- the object-action of a functor (objects + monotonicity).
ob-action : {D C : Cat} → Map D C → Σ f ꞉ (Ob D → Ob C) , is-monotone-ob f
ob-action F = Ob-map F , (λ x y h → Hom-map F x y h)

-- C is posetal: (1) thin homs, (2) the object-action is an equivalence,
-- (3) the objects form a set.
--
-- NB clause (3) makes faithful the Rocq `posetal_eq_isaprop` / hom-isaset
-- argument, which takes `isaset (Ob C)` as a SEPARATE hypothesis (Main.v
-- 3930) — posetality of the two clauses alone does NOT entail it (an
-- indiscrete category on a non-set is thin with the object action an
-- equivalence).  Bundling it here keeps the committed `posetal-hom-is-set`
-- signature (no extra argument) while staying honest, and is discharged
-- for 𝕀 and Δ n by `ob-𝕀-is-set` / `ob-Δ-is-set` (HLevels).
is-posetal : Cat → Type (𝓤₀ ⁺)
is-posetal C =
    ((x y : Ob C) → is-prop (Hom C x y))
  × ((D : Cat) → is-equiv (ob-action {D} {C}))
  × is-set (Ob C)

≃-sym : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → B ≃ A
≃-sym e = equiv-inv e ,
  invertible-to-equiv (equiv-inv e)
    (pr₁ e , equiv-inv-linv e , equiv-inv-rinv e)

-- monotonicity of an object-function is a proposition when the target is thin.
is-monotone-ob-is-prop : {D C : Cat}
  → ((x y : Ob C) → is-prop (Hom C x y))
  → (f : Ob D → Ob C) → is-prop (is-monotone-ob f)
is-monotone-ob-is-prop thin f =
  Π-is-prop (λ x → Π-is-prop (λ y → Π-is-prop (λ _ → thin (f x) (f y))))

------------------------------------------------------------------------
-- STREAM A deliverables — types fixed here, proofs below.
------------------------------------------------------------------------

-- Rocq `posetal_eq_objects` (Main.v 3919): in a posetal target a functor is
-- determined by its action on objects.  Needs only clauses (1),(2).
posetal-eq-objects : {A B : Cat} → is-posetal B → {f g : Map A B}
                   → ((x : Ob A) → comp f x ≡ comp g x) → f ≡ g
posetal-eq-objects {A} {B} H {f} {g} e =
  equiv-inj (ob-action {A} {B}) (pr₁ (pr₂ H) A)
    (to-Σ-≡ (funext e ,
             is-monotone-ob-is-prop (pr₁ H) (Ob-map g) _ _))

-- Rocq `posetal_eq_isaprop` / hom-isaset (Main.v 3930): a posetal target has
-- set-valued hom-types.  Reflexive prop-relation "agree on objects" detects
-- equality (clause 2 ⇒ posetal-eq-objects) and is a prop (clause 3); Hedberg.
posetal-hom-is-set : {A B : Cat} → is-posetal B → is-set (Map A B)
posetal-hom-is-set {A} {B} H = hedberg-set R Rprop ρ dec
  where
    R : Map A B → Map A B → Type 𝓤₀
    R f g = (x : Ob A) → comp f x ≡ comp g x
    Rprop : (f g : Map A B) → is-prop (R f g)
    Rprop f g = Π-is-prop (λ x → pr₂ (pr₂ H) (comp f x) (comp g x))
    ρ : (f : Map A B) → R f f
    ρ f x = refl (comp f x)
    dec : (f g : Map A B) → R f g → f ≡ g
    dec f g e = posetal-eq-objects H e

------------------------------------------------------------------------
-- I-posetal : 𝕀 is posetal  (Rocq `I_posetal`, Main.v ~4006+)
--
-- Clause (1) thin = `𝕀-thin`; clause (3) = `ob-𝕀-is-set`.  Clause (2),
-- `is-equiv (ob-action {D}{𝕀})`, is shown by an explicit two-sided inverse:
-- a monotone object-function f : Ob D → Ob 𝕀 transposes (via 𝕀-ob and
-- 𝕀-char-inverse) to a functor, and the round-trips are 𝕀-char-rinv/linv
-- plus injectivity of 𝕀-ob.
------------------------------------------------------------------------

I-posetal-clause2 : (D : Cat) → is-equiv (ob-action {D} {𝕀})
I-posetal-clause2 D =
  invertible-to-equiv (ob-action {D} {𝕀}) (inv , rinv , linv)
  where
    to𝟚 : (Ob D → Ob 𝕀) → (Ob D → 𝟚)
    to𝟚 f z = pr₁ 𝕀-ob (f z)

    -- monotone-on-objects ⇒ monotone-into-𝟚 (one direction suffices)
    m→ : (f : Ob D → Ob 𝕀) → is-monotone-ob f → is-monotone {D} (to𝟚 f)
    m→ f p m = 𝕀-hom-to-order (f (dom m)) (f (cod m))
                 (p (dom m) (cod m) (m , refl (dom m) , refl (cod m)))

    inv : (Σ f ꞉ (Ob D → Ob 𝕀) , is-monotone-ob f) → Map D 𝕀
    inv (f , p) = 𝕀-char-inverse D (to𝟚 f , m→ f p)

    rinv : (w : Σ f ꞉ (Ob D → Ob 𝕀) , is-monotone-ob f)
         → ob-action {D} {𝕀} (inv w) ≡ w
    rinv (f , p) =
      to-Σ-≡ (base , is-monotone-ob-is-prop 𝕀-thin f _ p)
      where
        rfact : 𝕀-char-comparison D (inv (f , p)) ≡ (to𝟚 f , m→ f p)
        rfact = 𝕀-char-rinv D (to𝟚 f , m→ f p)
        base : Ob-map (inv (f , p)) ≡ f
        base = funext (λ z →
          equiv-inj (pr₁ 𝕀-ob) (pr₂ 𝕀-ob) (ap (λ w → pr₁ w z) rfact))

    linv : (F : Map D 𝕀) → inv (ob-action {D} {𝕀} F) ≡ F
    linv F = ap (𝕀-char-inverse D) eqp ∙ 𝕀-char-linv D F
      where
        eqp : (to𝟚 (Ob-map F) , m→ (Ob-map F) (λ x y h → Hom-map F x y h))
              ≡ 𝕀-char-comparison D F
        eqp = to-Σ-≡ (refl _ , is-monotone-is-prop (ob-to-𝟚 F) _ _)

I-posetal : is-posetal 𝕀
I-posetal = 𝕀-thin , I-posetal-clause2 , ob-𝕀-is-set

------------------------------------------------------------------------
-- Delta-posetal : Δ n is posetal  (Rocq `Delta_posetal`, Main.v 3979)
--
-- Base n = 0 : Δ 0 = 𝟏c is posetal — its objects (Map 𝟏c 𝟏c) and morphisms
-- (Map 𝕀 𝟏c) are contractible, so both clauses and the object-set are
-- immediate.  Step n+1 : Δ(suc n) = Fun (Δ n) 𝕀, so `Fun-posetal _ 𝕀 I-posetal`.
------------------------------------------------------------------------

-- Hom 𝟏c is thin: the morphism (Map 𝕀 𝟏c) is unique by terminality and the
-- endpoint witnesses are paths in the set Ob 𝟏c.
𝟏c-thin : (x y : Ob 𝟏c) → is-prop (Hom 𝟏c x y)
𝟏c-thin x y (m1 , d1 , c1) (m2 , d2 , c2) =
  to-Σ-≡ (singletons-are-props (terminal 𝕀) m1 m2 ,
          ×-is-prop (ob-𝟏c-set (dom m2) x) (ob-𝟏c-set (cod m2) y) _ (d2 , c2))
  where
    ob-𝟏c-set : is-set (Ob 𝟏c)
    ob-𝟏c-set = props-are-sets (singletons-are-props (terminal 𝟏c))

is-posetal-𝟏c : is-posetal 𝟏c
is-posetal-𝟏c =
  𝟏c-thin , clause2 , props-are-sets (singletons-are-props (terminal 𝟏c))
  where
    clause2 : (D : Cat) → is-equiv (ob-action {D} {𝟏c})
    clause2 D = map-between-contrs-is-equiv (ob-action {D} {𝟏c})
      (terminal D)
      (Σ-prop-contr (fn-into-contr-is-contr (terminal 𝟏c))
        (is-monotone-ob-is-prop 𝟏c-thin) sec)
      where
        -- every object-function into Ob 𝟏c is monotone (identity squares)
        sec : (f : Ob D → Ob 𝟏c) → is-monotone-ob {D} {𝟏c} f
        sec f x y h =
          id-mor (f x) ,
          dom-id (f x) ,
          cod-id (f x) ∙ singletons-are-props (terminal 𝟏c) (f x) (f y)

-- For the simplex recursion only `Fun X 𝕀` (= Δ(suc n)) is needed, so we
-- specialise to C = 𝕀 (where the Interval machinery — 𝕀-char, mor-to-pointwise
-- — is available) rather than prove the general `Fun-posetal`.
--
-- Clause (3) — objects form a set — is proved here: Ob (Fun X 𝕀) ≃ Map X 𝕀 ≃
-- Monotone X (a set, being a Σ of (Ob X → 𝟚) and a propositional monotonicity
-- condition).
ob-FunX𝕀-is-set : (X : Cat) → is-set (Ob (Fun X 𝕀))
ob-FunX𝕀-is-set X =
  equiv-is-set (equiv-comp (ob-map-equiv X 𝕀) (𝕀-char X))
    (Σ-set-prop (fn-into-set 𝟚-is-set) (λ q → is-monotone-is-prop q))

-- maps into Fun X 𝕀 are determined on objects (engine of clause (1)),
-- proved directly from exp-equiv + `map-into-𝕀-eq` (so it does not depend on
-- thinness): the uncurried maps into 𝕀 agree wherever the originals do.
map-into-FunX𝕀-eq : (X A : Cat) (m1 m2 : Map A (Fun X 𝕀))
  → ((z : Ob A) → comp m1 z ≡ comp m2 z) → m1 ≡ m2
map-into-FunX𝕀-eq X A m1 m2 agree =
  equiv-inj (exp-comparison X 𝕀 A) (pr₂ (exp-equiv X 𝕀 A))
    (map-into-𝕀-eq (exp-comparison X 𝕀 A m1) (exp-comparison X 𝕀 A m2)
      (λ w → eval-lemma m1 w
           ∙ ap (λ φ → comp (ev X 𝕀) ⟨ φ , comp (π₂ A X) w ⟩)
                (agree (comp (π₁ A X) w))
           ∙ (eval-lemma m2 w) ⁻¹))
  where
    eval-lemma : (m : Map A (Fun X 𝕀)) (w : Ob (A ×c X))
      → comp (exp-comparison X 𝕀 A m) w
        ≡ comp (ev X 𝕀) ⟨ comp m (comp (π₁ A X) w) , comp (π₂ A X) w ⟩
    eval-lemma m w =
      composeA (ev X 𝕀) ⟨ comp m (π₁ A X) , π₂ A X ⟩ w
      ∙ ap (comp (ev X 𝕀))
          (pair-nat (comp m (π₁ A X)) (π₂ A X) w
           ∙ pair-ap (composeA m (π₁ A X) w) (refl _))

-- Clause (1): Hom (Fun X 𝕀) is thin  (Rocq `isaprop_Δn_edge`).  Two parallel
-- morphisms agree on the two objects of 𝕀 (endpoints), hence on all of Ob 𝕀
-- (val-𝕀), hence are equal; the witnesses are paths in the set Ob (Fun X 𝕀).
Fun-I-thin : (X : Cat) (x y : Ob (Fun X 𝕀)) → is-prop (Hom (Fun X 𝕀) x y)
Fun-I-thin X x y (m1 , d1 , c1) (m2 , d2 , c2) =
  to-Σ-≡ (m1≡m2 ,
          ×-is-prop (ob-FunX𝕀-is-set X (dom m2) x) (ob-FunX𝕀-is-set X (cod m2) y)
            _ (d2 , c2))
  where
    agree : (z : Ob 𝕀) → comp m1 z ≡ comp m2 z
    agree z = +-induction (λ _ → comp m1 z ≡ comp m2 z)
      (λ e0 → ap (comp m1) e0 ∙ d1 ∙ d2 ⁻¹ ∙ ap (comp m2) (e0 ⁻¹))
      (λ e1 → ap (comp m1) e1 ∙ c1 ∙ c2 ⁻¹ ∙ ap (comp m2) (e1 ⁻¹))
      (val-𝕀 z)
    m1≡m2 : m1 ≡ m2
    m1≡m2 = map-into-FunX𝕀-eq X 𝕀 m1 m2 agree

------------------------------------------------------------------------
-- Clause (2) for Fun X 𝕀  (Rocq `monotone_curry_delta`, Main.v 1922).
--
-- The object-action is shown an equivalence by an explicit curry/uncurry
-- between `Σ(Ob D → Ob(Fun X 𝕀)) is-monotone-ob` and
-- `Σ(Ob(D ×c X) → Ob 𝕀) is-monotone-ob` (the latter = source of
-- `I-posetal-clause2 (D ×c X)`), commuting with `exp-comparison`.
------------------------------------------------------------------------

