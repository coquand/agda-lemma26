{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Stage 3a: NbE for the free category on the 1-cells of Cat.
--
-- A `Tm A B` is a formal composite of atomic 1-cells (each atom is an
-- opaque `Map`).  Its normal form is the right-nested, unit-free list
-- of atoms (`Spine`).  `sound` is the canonical coherence cell taking a
-- term to its normal form, built once from composeA / comp-id-l/r.
--
-- Payoff: two terms with the SAME normal form are connected by `coh`,
-- so a pure associator/unitor reassociation becomes `coh s t (refl _)`
-- instead of an explicit composeA telescope.
------------------------------------------------------------------------

module Normaliser where

open import Spartan
open import CatAxioms
open import Coherence

------------------------------------------------------------------------
-- Syntax of formal composites and their denotation
------------------------------------------------------------------------

data Tm : Cat → Cat → Type (𝓤₀ ⁺) where
  ι    : {A B : Cat} → Map A B → Tm A B
  idt  : {A : Cat} → Tm A A
  _∘t_ : {A B C : Cat} → Tm B C → Tm A B → Tm A C

infixr 7 _∘t_

⟦_⟧ : {A B : Cat} → Tm A B → Map A B
⟦ ι f ⟧     = f
⟦ idt ⟧     = idMap _
⟦ s ∘t t ⟧  = comp ⟦ s ⟧ ⟦ t ⟧

------------------------------------------------------------------------
-- Normal forms = right-nested unit-free composites (typed lists)
------------------------------------------------------------------------

data Spine : Cat → Cat → Type (𝓤₀ ⁺) where
  []  : {A : Cat} → Spine A A
  _∷_ : {A B C : Cat} → Map B C → Spine A B → Spine A C

infixr 6 _∷_

emb : {A B : Cat} → Spine A B → Map A B
emb []       = idMap _
emb (f ∷ s)  = comp f (emb s)

_++_ : {A B C : Cat} → Spine B C → Spine A B → Spine A C
[]       ++ t = t
(f ∷ s)  ++ t = f ∷ (s ++ t)

infixr 6 _++_

nf : {A B : Cat} → Tm A B → Spine A B
nf (ι f)     = f ∷ []
nf idt       = []
nf (s ∘t t)  = nf s ++ nf t

-- append is associative and right-unital (left unit is definitional)
++-assoc : {A B C D : Cat} (σ : Spine C D) (τ : Spine B C) (υ : Spine A B)
         → (σ ++ τ) ++ υ ≡ σ ++ (τ ++ υ)
++-assoc []      τ υ = refl _
++-assoc (f ∷ σ) τ υ = ap (f ∷_) (++-assoc σ τ υ)

++-[] : {A B : Cat} (σ : Spine A B) → σ ++ [] ≡ σ
++-[] []      = refl _
++-[] (f ∷ σ) = ap (f ∷_) (++-[] σ)

------------------------------------------------------------------------
-- emb turns append into composition — the canonical reassociation
------------------------------------------------------------------------

emb-++ : {A B C : Cat} (σ : Spine B C) (τ : Spine A B)
       → comp (emb σ) (emb τ) ≡ emb (σ ++ τ)
emb-++ []       τ = comp-id-l (emb τ)
emb-++ (f ∷ σ)  τ = composeA f (emb σ) (emb τ) ∙ ccr f (emb-++ σ τ)

------------------------------------------------------------------------
-- Coherence of emb-++ (lax monoidality / Mac Lane's theorem core):
-- the two ways of multiplying a triple of spines agree, mediated by
-- the associator and the spine-level ++-assoc.  Base case = the
-- left-unit triangle (Id-triangle1 + IdKl-nat); cons case = the
-- pentagon induction (isolated below, then discharged).
------------------------------------------------------------------------

emb-++-assoc :
  {A B C D : Cat} (σ : Spine C D) (τ : Spine B C) (υ : Spine A B)
  → composeA (emb σ) (emb τ) (emb υ)
      ∙ ccr (emb σ) (emb-++ τ υ) ∙ emb-++ σ (τ ++ υ)
  ≡ ccl (emb υ) (emb-++ σ τ)
      ∙ emb-++ (σ ++ τ) υ ∙ ap emb (++-assoc σ τ υ)
emb-++-assoc [] τ υ =
    ∙-assoc (composeA (emb []) (emb τ) (emb υ))
            (ccr (emb []) (emb-++ τ υ)) (emb-++ [] (τ ++ υ))
  ∙ ap (composeA (emb []) (emb τ) (emb υ) ∙_) ((IdKl-nat (emb-++ τ υ)) ⁻¹)
  ∙ (∙-assoc (composeA (emb []) (emb τ) (emb υ))
             (comp-id-l (comp (emb τ) (emb υ))) (emb-++ τ υ)) ⁻¹
  ∙ ap (_∙ emb-++ τ υ) (Id-triangle1 (emb υ) (emb τ))
  ∙ (right-unit (ccl (emb υ) (comp-id-l (emb τ)) ∙ emb-++ τ υ)) ⁻¹
emb-++-assoc (f ∷ σ) τ υ = lhs≡mid ∙ mid≡rhs
  where
  W = emb σ ; Y = emb τ ; Z = emb υ ; M = emb-++ τ υ
  est = emb-++ σ τ ; esu = emb-++ (σ ++ τ) υ
  es  = emb-++ σ (τ ++ υ)
  aa  = ap emb (++-assoc σ τ υ)
  A1 = composeA (comp f W) Y Z
  A2 = composeA f W (comp Y Z)
  A3 = composeA f W (emb (τ ++ υ))
  A4 = composeA f (comp W Y) Z
  A5 = composeA f (emb (σ ++ τ)) Z
  P  = ccl Z (composeA f W Y)

  pent : A1 ∙ A2 ≡ P ∙ A4 ∙ ccr f (composeA W Y Z)
  pent = pentagonator f W Y Z

  nat3i : A2 ∙ ccr f (ccr W M) ≡ ccr (comp f W) M ∙ A3
  nat3i = compose-naturality3 f W M

  nat2i : A4 ∙ ccr f (ccl Z est) ≡ ccl Z (ccr f est) ∙ A5
  nat2i = compose-naturality2 f Z est

  IH : composeA W Y Z ∙ ccr W M ∙ es
     ≡ ccl Z est ∙ esu ∙ aa
  IH = emb-++-assoc σ τ υ

  -- ++-assoc on a cons distributes through emb as ccr f
  aa-cons : ap emb (++-assoc (f ∷ σ) τ υ) ≡ ccr f aa
  aa-cons = ap-comp emb (f ∷_) (++-assoc σ τ υ)
          ∙ (ap-comp (comp f) emb (++-assoc σ τ υ)) ⁻¹

  MID = P ∙ A4 ∙ ccr f (ccl Z est) ∙ ccr f esu ∙ ccr f aa

  -- L  ≡  MID : regroup, run nat3 backwards, pentagon, fold the ccr f's
  --            and the IH.  (the pentagon-powered half)
  lhs≡mid :
      composeA (emb (f ∷ σ)) (emb τ) (emb υ)
        ∙ ccr (emb (f ∷ σ)) (emb-++ τ υ) ∙ emb-++ (f ∷ σ) (τ ++ υ)
    ≡ MID
  lhs≡mid =
      (∙-assoc (A1 ∙ ccr (comp f W) M) A3 (ccr f es)) ⁻¹
    ∙ ap (λ z → z ∙ ccr f es)
         ( ∙-assoc A1 (ccr (comp f W) M) A3
         ∙ ap (A1 ∙_) (nat3i ⁻¹)
         ∙ (∙-assoc A1 A2 (ccr f (ccr W M))) ⁻¹
         ∙ ap (_∙ ccr f (ccr W M)) pent )
    ∙ ∙-assoc (P ∙ A4 ∙ ccr f (composeA W Y Z)) (ccr f (ccr W M)) (ccr f es)
    ∙ ap (λ z → (P ∙ A4 ∙ ccr f (composeA W Y Z)) ∙ z)
         ((ap-∙ (λ m → comp f m) (ccr W M) es) ⁻¹)
    ∙ ∙-assoc (P ∙ A4) (ccr f (composeA W Y Z)) (ccr f (ccr W M ∙ es))
    ∙ ap (λ z → (P ∙ A4) ∙ z)
         ( (ap-∙ (λ m → comp f m) (composeA W Y Z) (ccr W M ∙ es)) ⁻¹
         ∙ ap (λ z → ccr f z) ((∙-assoc (composeA W Y Z) (ccr W M) es) ⁻¹ ∙ IH)
         ∙ ap (λ z → ccr f z) (∙-assoc (ccl Z est) esu aa)
         ∙ ap-∙ (λ m → comp f m) (ccl Z est) (esu ∙ aa)
         ∙ ap (λ z → ccr f (ccl Z est) ∙ z) (ap-∙ (λ m → comp f m) esu aa) )
    ∙ (∙-assoc (P ∙ A4) (ccr f (ccl Z est)) (ccr f esu ∙ ccr f aa)) ⁻¹
    ∙ (∙-assoc ((P ∙ A4) ∙ ccr f (ccl Z est)) (ccr f esu) (ccr f aa)) ⁻¹

  -- MID  ≡  R : the single compose-naturality2 alignment, then fold back.
  mid≡rhs :
      MID
    ≡ ccl (emb υ) (emb-++ (f ∷ σ) τ)
        ∙ emb-++ ((f ∷ σ) ++ τ) υ ∙ ap emb (++-assoc (f ∷ σ) τ υ)
  mid≡rhs =
      ap (λ z → z ∙ ccr f esu ∙ ccr f aa)
         ( (∙-assoc P A4 (ccr f (ccl Z est)))
         ∙ ap (P ∙_) nat2i
         ∙ (∙-assoc P (ccl Z (ccr f est)) A5) ⁻¹ )
    ∙ ap (λ z → (P ∙ ccl Z (ccr f est) ∙ A5) ∙ ccr f esu ∙ z) (aa-cons ⁻¹)
    ∙ ap (λ z → z ∙ ap emb (++-assoc (f ∷ σ) τ υ))
         (∙-assoc (P ∙ ccl Z (ccr f est)) A5 (ccr f esu))
    ∙ ap (λ z → z ∙ emb-++ ((f ∷ σ) ++ τ) υ ∙ ap emb (++-assoc (f ∷ σ) τ υ))
         ((ap-∙ (λ m → comp m Z) (composeA f W Y) (ccr f est)) ⁻¹)

------------------------------------------------------------------------
-- Soundness: canonical coherence cell ⟦s⟧ ≡ emb (nf s)
------------------------------------------------------------------------

sound : {A B : Cat} (s : Tm A B) → ⟦ s ⟧ ≡ emb (nf s)
sound (ι f)     = (comp-id-r f) ⁻¹
sound idt       = refl _
sound (s ∘t t)  =
    ccl ⟦ t ⟧ (sound s)
  ∙ ccr (emb (nf s)) (sound t)
  ∙ emb-++ (nf s) (nf t)

------------------------------------------------------------------------
-- The coherence combinator: equal normal forms ⇒ equal 1-cells.
-- When nf s and nf t compute to the same spine, call `coh s t (refl _)`.
------------------------------------------------------------------------

coh : {A B : Cat} (s t : Tm A B) → nf s ≡ nf t → ⟦ s ⟧ ≡ ⟦ t ⟧
coh s t p = sound s ∙ ap emb p ∙ (sound t) ⁻¹

-- coh of the trivial spine-path is the identity 2-cell.
coh-refl : {A B : Cat} (s : Tm A B) → coh s s (refl _) ≡ refl ⟦ s ⟧
coh-refl s = ap (λ z → z ∙ (sound s) ⁻¹) (right-unit (sound s))
           ∙ right-inv (sound s)

-- coh, post-composed with the target's soundness cell, telescopes back.
coh-sound : {A B : Cat} (s t : Tm A B) (p : nf s ≡ nf t)
          → coh s t p ∙ sound t ≡ sound s ∙ ap emb p
coh-sound s t p =
    ∙-assoc (sound s ∙ ap emb p) ((sound t) ⁻¹) (sound t)
  ∙ ap (λ z → (sound s ∙ ap emb p) ∙ z) (left-inv (sound t))
  ∙ right-unit (sound s ∙ ap emb p)

-- coh composes: it is a functor from the discrete groupoid on spines.
coh-trans : {A B : Cat} (s t u : Tm A B)
            (p : nf s ≡ nf t) (q : nf t ≡ nf u)
          → coh s t p ∙ coh t u q ≡ coh s u (p ∙ q)
coh-trans s t u p q =
    ∙-assoc (sound s ∙ ap emb p) ((sound t) ⁻¹)
            ((sound t ∙ ap emb q) ∙ (sound u) ⁻¹)
  ∙ ap (λ z → (sound s ∙ ap emb p) ∙ z)
       ( ap (λ z → (sound t) ⁻¹ ∙ z)
            (∙-assoc (sound t) (ap emb q) ((sound u) ⁻¹))
       ∙ (∙-assoc ((sound t) ⁻¹) (sound t) (ap emb q ∙ (sound u) ⁻¹)) ⁻¹
       ∙ ap (λ z → z ∙ (ap emb q ∙ (sound u) ⁻¹)) (left-inv (sound t)) )
  ∙ (∙-assoc (sound s ∙ ap emb p) (ap emb q) ((sound u) ⁻¹)) ⁻¹
  ∙ ap (λ z → z ∙ (sound u) ⁻¹) (∙-assoc (sound s) (ap emb p) (ap emb q))
  ∙ ap (λ z → (sound s ∙ z) ∙ (sound u) ⁻¹) ((ap-∙ emb p q) ⁻¹)

-- Canonicity bridge for left-unit insertion: comp-id-l IS the coh cell.
-- (nf (idt ∘t a) = [] ++ nf a = nf a definitionally, so refl typechecks.)
unit-l-coh : {A B : Cat} (a : Tm A B)
           → comp-id-l ⟦ a ⟧ ≡ coh (idt ∘t a) a (refl _)
unit-l-coh a =
  cancel-right (sound a)
    ( IdKl-nat (sound a)
    ∙ (coh-sound (idt ∘t a) a (refl _) ∙ right-unit (sound (idt ∘t a))) ⁻¹ )

-- Associator naturality in all three slots at once (triple induction).
composeA-nat3 :
  {A B C D : Cat} {fa ga : Map C D} {fb gb : Map B C} {fc gc : Map A B}
  (sa : fa ≡ ga) (sb : fb ≡ gb) (sc : fc ≡ gc)
  → composeA fa fb fc
      ∙ (ccl (comp fb fc) sa ∙ ccr ga (ccl fc sb) ∙ ccr ga (ccr gb sc))
  ≡ (ccl fc (ccl fb sa) ∙ ccl fc (ccr ga sb) ∙ ccr (comp ga gb) sc)
      ∙ composeA ga gb gc
composeA-nat3 (refl _) (refl _) (refl _) = right-unit (composeA _ _ _)

-- Interchange (Godement); see PastingDSL.xch.
xch : {X Y Z : Cat} {m m' : Map Y Z} (q : m ≡ m') {a b : Map X Y} (F : a ≡ b)
    → ccr m F ∙ ccl b q ≡ ccl a q ∙ ccr m' F
xch (refl m) F = right-unit (ccr m F)

-- The associator bridge: the primitive associator IS the normaliser cell.
composeA-coh :
  {A B C D : Cat} (a : Tm C D) (b : Tm B C) (c : Tm A B)
  → composeA ⟦ a ⟧ ⟦ b ⟧ ⟦ c ⟧
  ≡ coh ((a ∘t b) ∘t c) (a ∘t (b ∘t c)) (++-assoc (nf a) (nf b) (nf c))
composeA-coh a b c =
  cancel-right (sound (a ∘t (b ∘t c)))
    ( star
    ∙ (coh-sound ((a ∘t b) ∘t c) (a ∘t (b ∘t c)) (++-assoc na nb nc)) ⁻¹ )
  where
  fa = ⟦ a ⟧ ; fb = ⟦ b ⟧ ; fc = ⟦ c ⟧
  na = nf a ; nb = nf b ; nc = nf c
  sa = sound a ; sb = sound b ; sc = sound c
  Ena = emb na ; Enb = emb nb ; Enc = emb nc
  Mbc = emb-++ nb nc ; Mab = emb-++ na nb
  E = ccr Ena Mbc
  F = emb-++ na (nb ++ nc)
  BL = ccl (comp fb fc) sa ∙ ccr Ena (ccl fc sb) ∙ ccr Ena (ccr Enb sc)
  BR = ccl fc (ccl fb sa) ∙ ccl fc (ccr Ena sb) ∙ ccr (comp Ena Enb) sc

  -- expand sound (a ∘t (b ∘t c)) by distributing ccr Ena over sound (b ∘t c)
  sr-exp : sound (a ∘t (b ∘t c)) ≡ BL ∙ E ∙ F
  sr-exp =
    ap (_∙ F)
      ( ap (ccl (comp fb fc) sa ∙_)
           ( ap-∙ (λ m → comp Ena m) (ccl fc sb ∙ ccr Enb sc) Mbc
           ∙ ap (_∙ E) (ap-∙ (λ m → comp Ena m) (ccl fc sb) (ccr Enb sc)) )
      ∙ (∙-assoc (ccl (comp fb fc) sa)
                 (ccr Ena (ccl fc sb) ∙ ccr Ena (ccr Enb sc)) E) ⁻¹
      ∙ ap (_∙ E) ((∙-assoc (ccl (comp fb fc) sa)
                            (ccr Ena (ccl fc sb)) (ccr Ena (ccr Enb sc))) ⁻¹) )

  -- expand sound ((a ∘t b) ∘t c); xch slides sound c past emb-++ na nb
  sl-exp : sound ((a ∘t b) ∘t c) ≡ BR ∙ ccl Enc Mab ∙ emb-++ (na ++ nb) nc
  sl-exp =
    ap (λ z → z ∙ ccr (emb (na ++ nb)) sc ∙ emb-++ (na ++ nb) nc)
       ( ap-∙ (λ m → comp m fc) (ccl fb sa ∙ ccr Ena sb) Mab
       ∙ ap (_∙ ccl fc Mab) (ap-∙ (λ m → comp m fc) (ccl fb sa) (ccr Ena sb)) )
    ∙ ap (_∙ emb-++ (na ++ nb) nc)
         ( ∙-assoc (ccl fc (ccl fb sa) ∙ ccl fc (ccr Ena sb)) (ccl fc Mab)
                   (ccr (emb (na ++ nb)) sc)
         ∙ ap (λ z → (ccl fc (ccl fb sa) ∙ ccl fc (ccr Ena sb)) ∙ z)
              ((xch Mab sc) ⁻¹)
         ∙ (∙-assoc (ccl fc (ccl fb sa) ∙ ccl fc (ccr Ena sb))
                    (ccr (comp Ena Enb) sc) (ccl Enc Mab)) ⁻¹ )

  star : composeA fa fb fc ∙ sound (a ∘t (b ∘t c))
       ≡ sound ((a ∘t b) ∘t c) ∙ ap emb (++-assoc na nb nc)
  star =
      ap (composeA fa fb fc ∙_) sr-exp
    ∙ ap (composeA fa fb fc ∙_) (∙-assoc BL E F)
    ∙ (∙-assoc (composeA fa fb fc) BL (E ∙ F)) ⁻¹
    ∙ ap (_∙ (E ∙ F)) (composeA-nat3 sa sb sc)
    ∙ ∙-assoc BR (composeA Ena Enb Enc) (E ∙ F)
    ∙ ap (BR ∙_)
         ( (∙-assoc (composeA Ena Enb Enc) E F) ⁻¹
         ∙ emb-++-assoc na nb nc )
    ∙ (∙-assoc BR (ccl Enc Mab ∙ emb-++ (na ++ nb) nc) (ap emb (++-assoc na nb nc))) ⁻¹
    ∙ ap (λ z → z ∙ ap emb (++-assoc na nb nc))
         ( (∙-assoc BR (ccl Enc Mab) (emb-++ (na ++ nb) nc)) ⁻¹ ∙ sl-exp ⁻¹ )

------------------------------------------------------------------------
-- Stage 3b status: canonicity / Mac Lane coherence — DONE.
--
-- Proved (zero postulates):
--   ++-assoc, ++-[]            spine lemmas
--   emb-++-assoc               coherence theorem core (pentagon induction)
--   composeA-nat3              associator naturality (3 slots at once)
--   composeA-coh               the ASSOCIATOR BRIDGE:
--     composeA ⟦a⟧⟦b⟧⟦c⟧ ≡ coh ((a∘tb)∘tc) (a∘t(b∘tc)) (++-assoc …)
--   unit-l-coh                 left-unit bridge (comp-id-l = coh)
--   coh-refl, coh-sound, coh-trans   coh functoriality
--
-- This is enough to rewrite any pure associator/left-unit telescope
-- termwise to a single coh (collapsing by coh-refl): e.g. an explicit
-- composeA is now provably the normaliser's cell (see NormaliserTest
-- `assoc-bridge`).
--
-- Optional remaining polish (only if a Stage-4 goal forces it):
--   comp-id-r ⟦a⟧ ≡ coh (a ∘t idt) a (++-[] (nf a))  — right-unit bridge;
--     its base case needs IdKrl (comp-id-l idMap ≡ comp-id-r idMap), an
--     extra axiom that prod_pent avoids, so prefer not to depend on it.
--   ccl/ccr-of-coh             whiskered-coh helpers (one-liners via ap).
------------------------------------------------------------------------
