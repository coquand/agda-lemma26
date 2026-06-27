{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Lemma 26, STREAM A — `is-posetal (Fun X 𝕀)` (Rocq `monotone_curry_delta`).
--
-- The object-action clause is proved by an explicit curry/uncurry
-- equivalence between functions Ob D → Ob(Fun X 𝕀) and Ob(D ×c X) → Ob 𝕀
-- (both cut down by monotonicity), commuting with `exp-comparison`.  Split
-- out of `PosetalCore` so the heavy elaboration sits behind a module
-- boundary (keeping each file's type-check well under budget).
------------------------------------------------------------------------

module FunIPosetal where

open import Spartan
open import CatAxioms
open import HigherCat using (𝕀; 𝕀-ob; 𝟚; Mor; equiv-inj)
open import Constructions using (Hom; Hom-map; dom; cod; id-mor; dom-id; cod-id;
  𝕀₀; 𝕀₁; dom-nat; cod-nat; funct-on-mor; equiv-inv)
open import Pullbacks using (_×c_; π₁; π₂; ⟨_,_⟩; pair-β₁; pair-β₂; pair-η;
  equiv-inv-rinv; equiv-inv-linv)
open import Exponentials using (Fun; ev; exp-comparison; exp-equiv;
  ob-to-map; map-to-ob; ob-map-roundtrip₁; ob-map-roundtrip₂)
open import Interval using (Δ; ob-to-𝟚; 𝕀-char-comparison;
  𝕀-char-inverse; 𝕀-char-linv; is-monotone; is-monotone-is-prop;
  invertible-to-equiv; ob-map-equiv; equiv-comp; pair-nat; pair-ap;
  _≤𝟚_; ≤𝟚-trans; ≤𝟚-transport; 𝕀-mor-order; mor-to-pointwise;
  pointwise-to-mor; 𝕀-char-ob-to-𝟚; Hom-coerce)
open import IntervalPosetal using (𝕀-thin; 𝕀-hom-to-order; 𝕀-order-to-hom)
open import FaceOrdCompat using (ev-point)
open import PosetalCore

module _ (X D : Cat) where
  prπ₁ : Ob (D ×c X) → Ob D
  prπ₁ u = comp (π₁ D X) u
  prπ₂ : Ob (D ×c X) → Ob X
  prπ₂ u = comp (π₂ D X) u

  -- uncurry on objects: (Ob D → Ob(Fun X 𝕀))  ↦  (Ob(D ×c X) → Ob 𝕀)
  uncurry-fn : (Ob D → Ob (Fun X 𝕀)) → Ob (D ×c X) → Ob 𝕀
  uncurry-fn f u = comp (ob-to-map X 𝕀 (f (prπ₁ u))) (prπ₂ u)

  -- the bifunctorial ≤𝟚 estimate for a morphism of D ×c X
  uncurry-mono-≤ : (f : Ob D → Ob (Fun X 𝕀)) → is-monotone-ob f
    → (m : Mor (D ×c X))
    → ob-to-𝟚 (ob-to-map X 𝕀 (f (prπ₁ (dom m)))) (prπ₂ (dom m))
      ≤𝟚 ob-to-𝟚 (ob-to-map X 𝕀 (f (prπ₁ (cod m)))) (prπ₂ (cod m))
  uncurry-mono-≤ f p m = ≤𝟚-trans step-i step-ii
    where
      mD : Mor D
      mD = comp (π₁ D X) m
      mX : Mor X
      mX = comp (π₂ D X) m
      πd : dom mD ≡ prπ₁ (dom m)
      πd = composeA (π₁ D X) m 𝕀₀
      πc : cod mD ≡ prπ₁ (cod m)
      πc = composeA (π₁ D X) m 𝕀₁
      πd2 : dom mX ≡ prπ₂ (dom m)
      πd2 = composeA (π₂ D X) m 𝕀₀
      πc2 : cod mX ≡ prπ₂ (cod m)
      πc2 = composeA (π₂ D X) m 𝕀₁
      -- (i) monotone in the functor argument (via f's monotonicity)
      homF : Hom (Fun X 𝕀) (f (prπ₁ (dom m))) (f (prπ₁ (cod m)))
      homF = p (prπ₁ (dom m)) (prπ₁ (cod m)) (mD , πd , πc)
      mF : Mor (Fun X 𝕀)
      mF = pr₁ homF
      step-i : ob-to-𝟚 (ob-to-map X 𝕀 (f (prπ₁ (dom m)))) (prπ₂ (dom m))
             ≤𝟚 ob-to-𝟚 (ob-to-map X 𝕀 (f (prπ₁ (cod m)))) (prπ₂ (dom m))
      step-i = ≤𝟚-transport
        (ap (λ φ → ob-to-𝟚 (ob-to-map X 𝕀 φ) (prπ₂ (dom m))) (pr₁ (pr₂ homF)))
        (ap (λ φ → ob-to-𝟚 (ob-to-map X 𝕀 φ) (prπ₂ (dom m))) (pr₂ (pr₂ homF)))
        (mor-to-pointwise X mF (prπ₂ (dom m)))
      -- (ii) monotone in the X argument (the functor f(cod) preserves order)
      φc : Ob (Fun X 𝕀)
      φc = f (prπ₁ (cod m))
      step-ii : ob-to-𝟚 (ob-to-map X 𝕀 φc) (prπ₂ (dom m))
              ≤𝟚 ob-to-𝟚 (ob-to-map X 𝕀 φc) (prπ₂ (cod m))
      step-ii = ≤𝟚-transport
        (ap (pr₁ 𝕀-ob) (dom-nat (ob-to-map X 𝕀 φc) mX)
         ∙ ap (ob-to-𝟚 (ob-to-map X 𝕀 φc)) πd2)
        (ap (pr₁ 𝕀-ob) (cod-nat (ob-to-map X 𝕀 φc) mX)
         ∙ ap (ob-to-𝟚 (ob-to-map X 𝕀 φc)) πc2)
        (𝕀-mor-order (comp (ob-to-map X 𝕀 φc) mX))

  -- lift the ≤𝟚 estimate to a morphism of 𝕀 (𝕀-order-to-hom)
  mono-uncurry : (f : Ob D → Ob (Fun X 𝕀)) → is-monotone-ob f
    → is-monotone-ob {D ×c X} {𝕀} (uncurry-fn f)
  mono-uncurry f p x y (m , dm , cm) =
    𝕀-order-to-hom (uncurry-fn f x) (uncurry-fn f y)
      (≤𝟚-transport (ap (λ u → pr₁ 𝕀-ob (uncurry-fn f u)) dm)
                    (ap (λ u → pr₁ 𝕀-ob (uncurry-fn f u)) cm)
                    (uncurry-mono-≤ f p m))

  Ψ : (Σ f ꞉ (Ob D → Ob (Fun X 𝕀)) , is-monotone-ob f)
    → (Σ g ꞉ (Ob (D ×c X) → Ob 𝕀) , is-monotone-ob g)
  Ψ (f , p) = uncurry-fn f , mono-uncurry f p

  -- a morphism of D ×c X out of a pair of component morphisms
  prod-mor : (mD : Mor D) (mX : Mor X)
    → Hom (D ×c X) ⟨ dom mD , dom mX ⟩ ⟨ cod mD , cod mX ⟩
  prod-mor mD mX = ⟨ mD , mX ⟩ , pair-nat mD mX 𝕀₀ , pair-nat mD mX 𝕀₁

  -- curry on objects: each d gives the monotone-into-𝟚 function b ↦ g⟨d,b⟩,
  -- whence a functor X → 𝕀 (an object of Fun X 𝕀)
  curry-qfun : (Ob (D ×c X) → Ob 𝕀) → Ob D → Ob X → 𝟚
  curry-qfun g d b = pr₁ 𝕀-ob (g ⟨ d , b ⟩)

  curry-qmono : (g : Ob (D ×c X) → Ob 𝕀) → is-monotone-ob g
    → (d : Ob D) → is-monotone {X} (curry-qfun g d)
  curry-qmono g q d m =
    𝕀-hom-to-order (g ⟨ d , dom m ⟩) (g ⟨ d , cod m ⟩)
      (q ⟨ d , dom m ⟩ ⟨ d , cod m ⟩
        (Hom-coerce (pair-ap (dom-id d) (refl (dom m)))
                    (pair-ap (cod-id d) (refl (cod m)))
                    (prod-mor (id-mor d) m)))

  curry-fn : (g : Ob (D ×c X) → Ob 𝕀) → is-monotone-ob g
    → Ob D → Ob (Fun X 𝕀)
  curry-fn g q d =
    map-to-ob X 𝕀 (𝕀-char-inverse X (curry-qfun g d , curry-qmono g q d))

  mono-curry : (g : Ob (D ×c X) → Ob 𝕀) (q : is-monotone-ob g)
    → is-monotone-ob {D} {Fun X 𝕀} (curry-fn g q)
  mono-curry g q x y (mD , dD , cD) =
    pointwise-to-mor X
      (𝕀-char-inverse X (curry-qfun g x , curry-qmono g q x))
      (𝕀-char-inverse X (curry-qfun g y , curry-qmono g q y))
      (λ b → ≤𝟚-transport
        (𝕀-char-ob-to-𝟚 X (curry-qfun g x , curry-qmono g q x) b ⁻¹)
        (𝕀-char-ob-to-𝟚 X (curry-qfun g y , curry-qmono g q y) b ⁻¹)
        (𝕀-hom-to-order (g ⟨ x , b ⟩) (g ⟨ y , b ⟩)
          (q ⟨ x , b ⟩ ⟨ y , b ⟩
            (Hom-coerce (pair-ap dD (dom-id b)) (pair-ap cD (cod-id b))
                        (prod-mor mD (id-mor b))))))

  Φ : (Σ g ꞉ (Ob (D ×c X) → Ob 𝕀) , is-monotone-ob g)
    → (Σ f ꞉ (Ob D → Ob (Fun X 𝕀)) , is-monotone-ob f)
  Φ (g , q) = curry-fn g q , mono-curry g q

  -- round-trips: uncurry ∘ curry = id (via ob-map / 𝕀-char round-trips,
  -- and pair-η collapsing the reassembled object)
  ΨΦ : (w : Σ g ꞉ (Ob (D ×c X) → Ob 𝕀) , is-monotone-ob g) → Ψ (Φ w) ≡ w
  ΨΦ (g , q) = to-Σ-≡ (funext base , is-monotone-ob-is-prop 𝕀-thin g _ _)
    where
      base : (u : Ob (D ×c X)) → uncurry-fn (curry-fn g q) u ≡ g u
      base u =
        ap (λ h → comp h (prπ₂ u))
           (ob-map-roundtrip₁ X 𝕀
             (𝕀-char-inverse X
               (curry-qfun g (prπ₁ u) , curry-qmono g q (prπ₁ u))))
        ∙ equiv-inj (pr₁ 𝕀-ob) (pr₂ 𝕀-ob)
            (𝕀-char-ob-to-𝟚 X
               (curry-qfun g (prπ₁ u) , curry-qmono g q (prπ₁ u)) (prπ₂ u)
             ∙ ap (pr₁ 𝕀-ob) (ap g (pair-η u)))

  ΦΨ : (w : Σ f ꞉ (Ob D → Ob (Fun X 𝕀)) , is-monotone-ob f) → Φ (Ψ w) ≡ w
  ΦΨ (f , p) =
    to-Σ-≡ (funext base2 , is-monotone-ob-is-prop (Fun-I-thin X) f _ _)
    where
      base2 : (d : Ob D)
            → curry-fn (uncurry-fn f) (mono-uncurry f p) d ≡ f d
      base2 d =
        equiv-inj (ob-to-map X 𝕀) (pr₂ (ob-map-equiv X 𝕀))
          (ob-map-roundtrip₁ X 𝕀
             (𝕀-char-inverse X
               (curry-qfun (uncurry-fn f) d
               , curry-qmono (uncurry-fn f) (mono-uncurry f p) d))
           ∙ ap (𝕀-char-inverse X) eqcomp
           ∙ 𝕀-char-linv X (ob-to-map X 𝕀 (f d)))
        where
          eqcomp : (curry-qfun (uncurry-fn f) d
                   , curry-qmono (uncurry-fn f) (mono-uncurry f p) d)
                 ≡ 𝕀-char-comparison X (ob-to-map X 𝕀 (f d))
          eqcomp = to-Σ-≡ (funext pweq ,
            is-monotone-is-prop (ob-to-𝟚 (ob-to-map X 𝕀 (f d))) _ _)
            where
              pweq : (b : Ob X)
                   → curry-qfun (uncurry-fn f) d b
                     ≡ ob-to-𝟚 (ob-to-map X 𝕀 (f d)) b
              pweq b = ap (pr₁ 𝕀-ob)
                ( ap (λ a → comp (ob-to-map X 𝕀 (f a)) (comp (π₂ D X) ⟨ d , b ⟩))
                     (pair-β₁ d b)
                ∙ ap (comp (ob-to-map X 𝕀 (f d))) (pair-β₂ d b) )

  -- the is-equiv component is kept `opaque` so that `equiv-inv ψ-equiv`
  -- below stays symbolic — forcing it would unfold the half-adjoint
  -- coherence built on the round-trips (a large normalisation).
  opaque
    ψ-is-equiv : is-equiv Ψ
    ψ-is-equiv = invertible-to-equiv Ψ (Φ , ΨΦ , ΦΨ)

  ψ-equiv : (Σ f ꞉ (Ob D → Ob (Fun X 𝕀)) , is-monotone-ob f)
          ≃ (Σ g ꞉ (Ob (D ×c X) → Ob 𝕀) , is-monotone-ob g)
  ψ-equiv = Ψ , ψ-is-equiv

  -- the square: uncurry ∘ object-action = object-action ∘ exp-comparison,
  -- via `ev-point` (evaluation = ev on a pair) and the exp-comparison eval
  sq : (F : Map D (Fun X 𝕀))
     → Ψ (ob-action {D} {Fun X 𝕀} F)
       ≡ ob-action {D ×c X} {𝕀} (exp-comparison X 𝕀 D F)
  sq F = to-Σ-≡ (funext sqbase , is-monotone-ob-is-prop 𝕀-thin _ _ _)
    where
      sqbase : (u : Ob (D ×c X))
             → uncurry-fn (Ob-map F) u ≡ comp (exp-comparison X 𝕀 D F) u
      sqbase u =
        ev-point X 𝕀 (comp F (prπ₁ u)) (prπ₂ u)
        ∙ ( composeA (ev X 𝕀) ⟨ comp F (π₁ D X) , π₂ D X ⟩ u
          ∙ ap (comp (ev X 𝕀))
              (pair-nat (comp F (π₁ D X)) (π₂ D X) u
               ∙ pair-ap (composeA F (π₁ D X) u) (refl _)) ) ⁻¹

  -- Clause (2), assembled: `ob-action` is homotopic to the composite
  -- (exp-comparison ; ob-action_{D×cX} ; uncurry⁻¹) of three equivalences.
  Fun-I-clause2 : is-equiv (ob-action {D} {Fun X 𝕀})
  Fun-I-clause2 = transport is-equiv (funext htpy) (pr₂ E)
    where
      E : Map D (Fun X 𝕀) ≃ (Σ f ꞉ (Ob D → Ob (Fun X 𝕀)) , is-monotone-ob f)
      E = equiv-comp
            (equiv-comp (exp-equiv X 𝕀 D)
              (ob-action {D ×c X} {𝕀} , I-posetal-clause2 (D ×c X)))
            (≃-sym ψ-equiv)
      htpy : (F : Map D (Fun X 𝕀)) → pr₁ E F ≡ ob-action {D} {Fun X 𝕀} F
      htpy F =
        ap (equiv-inv ψ-equiv) (sq F ⁻¹)
        ∙ equiv-inv-linv ψ-equiv (ob-action {D} {Fun X 𝕀} F)

Fun-I-posetal : (X : Cat) → is-posetal (Fun X 𝕀)
Fun-I-posetal X = Fun-I-thin X , Fun-I-clause2 X , ob-FunX𝕀-is-set X
