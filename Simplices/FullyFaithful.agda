{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- axioms.pdf results 33–39: fully faithful functors, invertible
-- morphisms, the Rezk axiom, "𝕀 detects equivalences", and the
-- characterisation of invertible functors.
--
--   Def 33  Fully faithful functors                       [DEFINED]
--   Def 34  Invertible morphisms                          [DEFINED]
--   Lem 35  Fully faithful functors reflect isomorphisms  [PROVED]
--   Ax  36  The Rezk axiom (categories are univalent)     [POSTULATE — axiom]
--   Lem 37  A ff functor induces an embedding on objects  [PROVED]
--   Ax  38  𝕀 detects equivalences                        [POSTULATE — axiom]
--   Rem 39  invertible ⇔ fully faithful + surjective      [POSTULATE — TODO]
--
-- The PROVED lemmas rely on three *constructible* coherences that
-- Remark 32 of axioms.pdf says are always built explicitly (functor
-- preserves identities / composition of morphisms; inverses are
-- unique).  Constructing them needs the Σ-path bookkeeping in `Hom`
-- (Ob B need not be a set), so they are isolated as clearly-labelled
-- postulates below — they are NOT new admissible axioms.  The only
-- genuine new axioms are 36 (Rezk) and 38 (𝕀 detects equivalences).
------------------------------------------------------------------------

module Simplices.FullyFaithful where

open import Foundations.Spartan
open import Category.CatAxioms
open import Category.HigherCat
open import Category.Constructions
open import Category.Pullbacks using (equiv-inv-rinv; equiv-inv-linv)
open import Interval.Interval using (equiv-comp; invertible-to-equiv)
open import Foundations.SigmaEquiv using (Σ-change-of-base; Σ-fiberwise-equiv)
open import Foundations.Coherence
open import Solvers.GroupoidSolver using (Expr; ι; ε; _⊕_; eval; solveG) renaming (inv to invE)
open import Simplices.Segal using (comp-hom; comp-mor; dom-comp-mor; cod-comp-mor;
  funct-pres-id; right-unit-d₀₂; left-unit-d₀₂; comp-witness-long; segal-first;
  segal-second; segal-linv; segal-comparison; segal-witness)

------------------------------------------------------------------------
-- Hom-equality from a Mor-path + two endpoint 2-cells (Ob C need not be
-- a set, so the dom/cod proofs must be matched explicitly).
------------------------------------------------------------------------

to-×-≡' : {A : Type 𝓤} {B : Type 𝓥} {a a' : A} {b b' : B}
        → a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
to-×-≡' (refl _) (refl _) = refl _

Hom-≡ : {C : Cat} {x y : Ob C} {m m' : Mor C}
  {p : dom m ≡ x} {q : cod m ≡ y} {p' : dom m' ≡ x} {q' : cod m' ≡ y}
  (α : m ≡ m') → p ≡ ap dom α ∙ p' → q ≡ ap cod α ∙ q'
  → _≡_ {A = Hom C x y} (m , p , q) (m' , p' , q')
Hom-≡ (refl _) hp hq = ap (λ pq → _ , pq) (to-×-≡' hp hq)

-- The shared dom/cod endpoint coherence (ι = 𝕀₀ for dom, 𝕀₁ for cod):
-- "functors respect the identity-morphism endpoint proofs".  Proof is a
-- single Mac Lane pentagon (pentagonator) + reassociator naturality
-- (compose-naturality3) + the right-unit triangle (Id-triangle3).
T! : (v : Ob 𝕀) → comp (! 𝕀) v ≡ idMap 𝟏c
T! v = singletons-are-props (terminal 𝟏c) (comp (! 𝕀) v) (idMap 𝟏c)

endpt : {A B : Cat} (f : Map A B) (a : Ob A) (v : Ob 𝕀)
  → composeA f (comp a (! 𝕀)) v
      ∙ ap (comp f) (composeA a (! 𝕀) v ∙ ap (comp a) (T! v) ∙ comp-id-r a)
  ≡ ap (λ m → comp m v) (comp-assoc f a (! 𝕀))
      ∙ (composeA (comp f a) (! 𝕀) v ∙ ap (comp (comp f a)) (T! v)
         ∙ comp-id-r (comp f a))
endpt {A} {B} f a v =
  begin
    M ∙ ap (comp f) ((X ∙ caT) ∙ ura)
  ≡⟨ ap (M ∙_) (ap-∙ (comp f) (X ∙ caT) ura
                ∙ ap (λ w → w ∙ ap (comp f) ura) (ap-∙ (comp f) X caT)) ⟩
    M ∙ ((N ∙ fcaT) ∙ fura)
  ≡⟨ solveG (v' M ⊕ ((v' N ⊕ v' fcaT) ⊕ v' fura))
            ((v' M ⊕ v' N) ⊕ (v' fcaT ⊕ v' fura)) (refl _) ⟩
    (M ∙ N) ∙ (fcaT ∙ fura)
  ≡⟨ ap (λ w → w ∙ (fcaT ∙ fura)) mn ⟩
    (lead ∙ (P ∙ Q)) ∙ (fcaT ∙ fura)
  ≡⟨ solveG ((v' lead ⊕ (v' P ⊕ v' Q)) ⊕ (v' fcaT ⊕ v' fura))
            (((v' lead ⊕ v' P) ⊕ (v' Q ⊕ v' fcaT)) ⊕ v' fura) (refl _) ⟩
    ((lead ∙ P) ∙ (Q ∙ fcaT)) ∙ fura
  ≡⟨ ap (λ w → ((lead ∙ P) ∙ w) ∙ fura) nat3 ⟩
    ((lead ∙ P) ∙ (TT ∙ R)) ∙ fura
  ≡⟨ solveG (((v' lead ⊕ v' P) ⊕ (v' TT ⊕ v' R)) ⊕ v' fura)
            (((v' lead ⊕ v' P) ⊕ v' TT) ⊕ (v' R ⊕ v' fura)) (refl _) ⟩
    (((lead ∙ P) ∙ TT) ∙ (R ∙ fura))
  ≡⟨ ap (λ w → ((lead ∙ P) ∙ TT) ∙ w) tri ⟩
    (((lead ∙ P) ∙ TT) ∙ U)
  ≡⟨ solveG ((((v' lead ⊕ v' P) ⊕ v' TT) ⊕ v' U))
            (v' lead ⊕ ((v' P ⊕ v' TT) ⊕ v' U)) (refl _) ⟩
    lead ∙ ((P ∙ TT) ∙ U)
  ∎
  where
    v' : {x y : Map 𝟏c B} → x ≡ y → Expr x y
    v' = ι
    X    = composeA a (! 𝕀) v
    caT  = ap (comp a) (T! v)
    ura  = comp-id-r a
    M    = composeA f (comp a (! 𝕀)) v
    N    = ap (comp f) X
    fcaT = ap (comp f) caT
    fura = ap (comp f) ura
    P    = composeA (comp f a) (! 𝕀) v
    Q    = composeA f a (comp (! 𝕀) v)
    L1   = ap (λ m → comp m v) (composeA f a (! 𝕀))
    lead = ap (λ m → comp m v) (comp-assoc f a (! 𝕀))
    TT   = ap (comp (comp f a)) (T! v)
    R    = composeA f a (idMap 𝟏c)
    U    = comp-id-r (comp f a)
    l1eq : L1 ≡ lead ⁻¹
    l1eq = ap-⁻¹ (λ m → comp m v) (comp-assoc f a (! 𝕀))
    pent : P ∙ Q ≡ (L1 ∙ M) ∙ N
    pent = pentagonator f a (! 𝕀) v
    nat3 : Q ∙ fcaT ≡ TT ∙ R
    nat3 = compose-naturality3 f a (T! v)
    tri : R ∙ fura ≡ U
    tri = Id-triangle3 a f
    mn : M ∙ N ≡ lead ∙ (P ∙ Q)
    mn =
        ap (λ w → w ∙ (M ∙ N)) ((right-inv lead) ⁻¹)
      ∙ solveG ((v' lead ⊕ invE (v' lead)) ⊕ (v' M ⊕ v' N))
               (v' lead ⊕ (invE (v' lead) ⊕ (v' M ⊕ v' N))) (refl _)
      ∙ ap (lead ∙_)
          ( ap (λ w → w ∙ (M ∙ N)) (l1eq ⁻¹)
          ∙ solveG (v' L1 ⊕ (v' M ⊕ v' N)) ((v' L1 ⊕ v' M) ⊕ v' N) (refl _)
          ∙ pent ⁻¹ )

Hom-map-id : {A B : Cat} (f : Map A B) (a : Ob A)
  → Hom-map f a a (id-hom a) ≡ id-hom (Ob-map f a)
Hom-map-id f a = Hom-≡ (funct-pres-id f a) (endpt f a 𝕀₀) (endpt f a 𝕀₁)

------------------------------------------------------------------------
-- Small HoTT helpers (not already in the prelude)
------------------------------------------------------------------------

is-embedding : {A : Type 𝓤} {B : Type 𝓥} → (A → B) → Type (𝓤 ⊔ 𝓥)
is-embedding {A = A} f = (x y : A) → is-equiv (λ (p : x ≡ y) → ap f p)

homotopic-is-equiv : {A : Type 𝓤} {B : Type 𝓥} {f g : A → B}
  → (f ∼ g) → is-equiv f → is-equiv g
homotopic-is-equiv h ef = transport is-equiv (funext h) ef

≃-sym : {A : Type 𝓤} {B : Type 𝓥} → A ≃ B → B ≃ A
≃-sym e = equiv-inv e ,
  invertible-to-equiv (equiv-inv e) (pr₁ e , equiv-inv-linv e , equiv-inv-rinv e)

-- biimplication between propositions is an equivalence.
prop-equiv : {P : Type 𝓤} {Q : Type 𝓥}
  → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≃ Q
prop-equiv pP pQ to from =
  to , λ q → (from q , pQ (to (from q)) q) ,
    λ { (p , e) → to-Σ-≡ (pP (from q) p , props-are-sets pQ _ _ _ e) }

------------------------------------------------------------------------
-- Definition 33: Fully faithful functors  [0010]
--
-- f : A → B is fully faithful if its action on every mapping space
-- `Hom-map f a₀ a₁ : A(a₀,a₁) → B(f a₀, f a₁)` is an equivalence.
------------------------------------------------------------------------

is-ff : {A B : Cat} → Map A B → Type 𝓤₀
is-ff {A} f = (a₀ a₁ : Ob A) → is-equiv (Hom-map f a₀ a₁)

------------------------------------------------------------------------
-- Definition 34: Invertible morphisms  [001R]
--
-- We take the two-sided-inverse formulation (condition 1).  A morphism
-- f : C(a,b) is invertible if there is g : C(b,a) with g∘f = id_a and
-- f∘g = id_b.  (Conditions 2 and 3 — precomposition / postcomposition
-- being equivalences — are the equivalent reformulations; we do not
-- need them explicitly downstream.)
------------------------------------------------------------------------

is-inv-mor : {C : Cat} {a b : Ob C} → Hom C a b → Type 𝓤₀
is-inv-mor {C} {a} {b} f =
  Σ g ꞉ Hom C b a , (comp-hom f g ≡ id-hom a) × (comp-hom g f ≡ id-hom b)

-- isomorphism of objects: an invertible morphism between them.
_≅ₒ_ : {C : Cat} → Ob C → Ob C → Type 𝓤₀
_≅ₒ_ {C} a b = Σ f ꞉ Hom C a b , is-inv-mor f

------------------------------------------------------------------------
-- Constructible coherences (Remark 32 [001L]) — NOT new axioms.
--
-- A functor preserves identity and composition of morphisms, and
-- inverses are unique.  All three are built explicitly in the headcanon
-- (from `funct-pres-id`, `comp-witness-long`, and the unit/associativity
-- laws of `comp-hom`); we isolate them here to avoid the Σ-path algebra
-- in `Hom` (whose fibres are paths in the not-necessarily-set Ob B).
------------------------------------------------------------------------

postulate
  -- functor preserves composition of morphisms (comp-witness-long)
  Hom-map-comp : {A B : Cat} (f : Map A B) {a b c : Ob A}
    (u : Hom A a b) (v : Hom A b c)
    → Hom-map f a c (comp-hom u v)
      ≡ comp-hom (Hom-map f a b u) (Hom-map f b c v)
  -- identities are invertible (unit law for comp-hom)
  id-hom-is-inv : {C : Cat} (a : Ob C) → is-inv-mor (id-hom a)
  -- invertibility is a proposition (uniqueness of inverses)
  is-inv-mor-is-prop : {C : Cat} {a b : Ob C} (f : Hom C a b)
    → is-prop (is-inv-mor f)

------------------------------------------------------------------------
-- Every functor preserves invertibility (no full-faithfulness needed):
-- the image of an inverse is an inverse of the image.
------------------------------------------------------------------------

ff-pres-inv : {A B : Cat} (F : Map A B) {a b : Ob A} (f : Hom A a b)
  → is-inv-mor f → is-inv-mor (Hom-map F a b f)
ff-pres-inv F {a} {b} f (g , p , q) =
  Hom-map F b a g ,
  ( (Hom-map-comp F f g) ⁻¹ ∙ ap (Hom-map F a a) p ∙ Hom-map-id F a ) ,
  ( (Hom-map-comp F g f) ⁻¹ ∙ ap (Hom-map F b b) q ∙ Hom-map-id F b )

------------------------------------------------------------------------
-- Lemma 35: Fully faithful functors reflect isomorphisms  [001S]
--
-- If F(f) is invertible then so is f.  Pull the inverse back along the
-- ff equivalence, then check the two unit equations by applying F (an
-- embedding on Hom) and using that F preserves id and composition.
------------------------------------------------------------------------

ff-reflects-inv : {A B : Cat} (F : Map A B) → is-ff F
  → {a b : Ob A} (f : Hom A a b)
  → is-inv-mor (Hom-map F a b f) → is-inv-mor f
ff-reflects-inv {A} {B} F ff {a} {b} f (G , Gr , Gl) =
  g , left , right
  where
    e-ba : Hom A b a ≃ Hom B (Ob-map F b) (Ob-map F a)
    e-ba = Hom-map F b a , ff b a

    g : Hom A b a
    g = equiv-inv e-ba G

    Fg≡G : Hom-map F b a g ≡ G
    Fg≡G = equiv-inv-rinv e-ba G

    left : comp-hom f g ≡ id-hom a
    left = equiv-inj (Hom-map F a a) (ff a a)
      ( Hom-map-comp F f g
      ∙ ap (comp-hom (Hom-map F a b f)) Fg≡G
      ∙ Gr
      ∙ (Hom-map-id F a) ⁻¹ )

    right : comp-hom g f ≡ id-hom b
    right = equiv-inj (Hom-map F b b) (ff b b)
      ( Hom-map-comp F g f
      ∙ ap (λ z → comp-hom z (Hom-map F a b f)) Fg≡G
      ∙ Gl
      ∙ (Hom-map-id F b) ⁻¹ )

------------------------------------------------------------------------
-- Axiom 36: The Rezk axiom — categories are univalent  [001Q]
--
-- The map (a ≡ b) → (a ≅ₒ b) sending refl to the identity isomorphism
-- is an equivalence.  (This is the embedding-with-image form of the
-- PDF, packaged as univalence of objects, which is what Lemma 37 uses.)
------------------------------------------------------------------------

idtoiso : {C : Cat} {a b : Ob C} → a ≡ b → a ≅ₒ b
idtoiso {C} {a} (refl _) = id-hom a , id-hom-is-inv a

postulate
  rezk : (C : Cat) (a b : Ob C) → is-equiv (idtoiso {C} {a} {b})

------------------------------------------------------------------------
-- Lemma 37: A fully faithful functor induces an embedding on objects [001P]
--
-- ap (Ob-map F) : (a₀ ≡ a₁) → (F a₀ ≡ F a₁) factors, through the Rezk
-- equivalences idtoiso, as the action on isomorphisms
--   isoact : (a₀ ≅ₒ a₁) → (F a₀ ≅ₒ F a₁),
-- which is an equivalence because F preserves invertibility (ff-pres-inv)
-- and reflects it (Lemma 35), and invertibility is a proposition.  Hence
-- ap (Ob-map F) is an equivalence, i.e. Ob-map F is an embedding.
------------------------------------------------------------------------

module _ {A B : Cat} (F : Map A B) (ff : is-ff F) where

  isoact : {a₀ a₁ : Ob A} → (a₀ ≅ₒ a₁) → (Ob-map F a₀ ≅ₒ Ob-map F a₁)
  isoact {a₀} {a₁} (f , inv) = Hom-map F a₀ a₁ f , ff-pres-inv F f inv

  -- isoact is an equivalence: Σ-functor over the ff-equivalence on Hom,
  -- with a fibrewise prop-equivalence on invertibility.
  isoact-equiv : (a₀ a₁ : Ob A) → is-equiv (isoact {a₀} {a₁})
  isoact-equiv a₀ a₁ = homotopic-is-equiv (λ _ → refl _) (pr₂ e-iso)
    where
      fib : (f : Hom A a₀ a₁)
          → is-inv-mor f ≃ is-inv-mor (Hom-map F a₀ a₁ f)
      fib f = prop-equiv (is-inv-mor-is-prop f)
                         (is-inv-mor-is-prop (Hom-map F a₀ a₁ f))
                         (ff-pres-inv F f) (ff-reflects-inv F ff f)
      e-iso : (a₀ ≅ₒ a₁) ≃ (Ob-map F a₀ ≅ₒ Ob-map F a₁)
      e-iso = equiv-comp (Σ-fiberwise-equiv fib)
                         (Σ-change-of-base (Hom-map F a₀ a₁ , ff a₀ a₁))

  -- the Rezk square: idtoiso ∘ ap(Ob-map F) = isoact ∘ idtoiso.
  rezk-square : {a₀ a₁ : Ob A} (p : a₀ ≡ a₁)
    → idtoiso (ap (Ob-map F) p) ≡ isoact (idtoiso p)
  rezk-square {a₀} (refl _) =
    to-Σ-≡ ((Hom-map-id F a₀) ⁻¹ , is-inv-mor-is-prop _ _ _)

  ff-emb-on-ob : is-embedding (Ob-map F)
  ff-emb-on-ob a₀ a₁ = homotopic-is-equiv (λ p → (htpy p) ⁻¹) (pr₂ e-total)
    where
      eA : (a₀ ≡ a₁) ≃ (a₀ ≅ₒ a₁)
      eA = idtoiso , rezk A a₀ a₁
      eB : (Ob-map F a₀ ≡ Ob-map F a₁) ≃ (Ob-map F a₀ ≅ₒ Ob-map F a₁)
      eB = idtoiso , rezk B (Ob-map F a₀) (Ob-map F a₁)
      e-total : (a₀ ≡ a₁) ≃ (Ob-map F a₀ ≡ Ob-map F a₁)
      e-total = equiv-comp eA
                  (equiv-comp ((isoact {a₀} {a₁}) , isoact-equiv a₀ a₁)
                              (≃-sym eB))
      -- ap(Ob-map F) is homotopic to the composite forward map.
      htpy : (p : a₀ ≡ a₁) → ap (Ob-map F) p ≡ pr₁ e-total p
      htpy p =
          (equiv-inv-linv eB (ap (Ob-map F) p)) ⁻¹
        ∙ ap (equiv-inv eB) (rezk-square p)

------------------------------------------------------------------------
-- Axiom 38: 𝕀 detects equivalences  [001M]
--
-- If postcomposition  Map(𝕀, A) → Map(𝕀, B)  is an equivalence then the
-- functor f : A → B is an isomorphism.
------------------------------------------------------------------------

postulate
  𝕀-detects-equiv : {A B : Cat} (f : Map A B)
    → is-equiv (post-comp f 𝕀) → isIso f

------------------------------------------------------------------------
-- Remark 39: A functor is invertible iff fully faithful and surjective
-- on objects  [001N]
--
-- TODO / UNPROVED.  The headcanon derives this from Axiom 38 together
-- with: 𝟏c is a retract of 𝕀 (so equivalences are closed under retracts,
-- `retract-of-equiv` in Squares.SquareAlg) giving that an invertible
-- `post-comp f 𝕀` forces invertible `Ob-map f`; and the fibrewise
-- analysis `post-comp f 𝕀 is invertible ⇔ f is fully faithful` over
-- Ob(A)².  Assembling the two directions (and the type-theoretic notion
-- of "surjective on objects", which needs propositional truncation not
-- present in the prelude) is left as future work.  Stated here with a
-- split-surjectivity hypothesis to fix the interface.
------------------------------------------------------------------------

is-split-surj-on-ob : {A B : Cat} → Map A B → Type 𝓤₀
is-split-surj-on-ob {A} {B} f = (b : Ob B) → Σ a ꞉ Ob A , Ob-map f a ≡ b

postulate
  -- UNPROVED (see comment): ff + split-surjective-on-objects ⇒ invertible.
  ff-surj-invertible : {A B : Cat} (f : Map A B)
    → is-ff f → is-split-surj-on-ob f → isIso f
