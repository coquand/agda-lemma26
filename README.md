# agda-lemma26

An Agda formalization of **Lemma 26** in the pushout-square formulation:
for every `n`, the gluing square

```
        𝟏c ──────▶ Δ¹
        │           │
        ▼           ▼
        Δⁿ ─────▶ Δ⁽ⁿ⁺¹⁾
```

is a pushout. The main theorem is

```agda
lemma26-square : (n : ℕ) → is-pushout-square (Sq (suc n))
```

in `Pushout.agda`, proved by induction on `n`: a base case `Sq (suc zero)`
(derived from the Segal/Rezk axiom) and an inductive step that transports the
pushout property along the `Δⁿ × 𝕀` retraction (`S-step`).

## Context

This formalization is part of the axiom system for higher categories of
**Christian Sattler** and **David Wärn**, inspired by the work of the group of
**Denis-Charles Cisinski**.

## Building

The repository is an Agda library (`lemma26.agda-lib`, source root `.`). The
entry point is `Pushout.agda`; type-checking it checks the whole development:

```sh
agda Pushout.agda
```

Tested with **Agda 2.8.0** and **Agda 2.9.0** (a cold build of the full
~46-module cone takes ≈26 s on 2.8.0, ≈14 s on 2.9.0). Every file is
`{-# OPTIONS --without-K --exact-split #-}`.

## What is assumed

The development is postulate-free except for its **admissible axioms**: the
intended categorical/HoTT input of the Sattler–Wärn system, not gaps in the
proof. They are the only `postulate`s in the live code, listed in full below
(implicit arguments elided for readability).

### HoTT foundations — `Foundations/Spartan.agda`

```agda
funext     : f ∼ g → f ≡ g                         -- function extensionality
univalence : is-equiv (id-to-equiv A B)            -- the univalence axiom
```

### Ambient (wild) category — `Category/CatAxioms.agda`

```agda
Cat        : Type (𝓤₀ ⁺)                           -- the type of categories
Map        : Cat → Cat → Type 𝓤₀                   -- functors / maps
comp       : Map B C → Map A B → Map A C            -- composition (comp f g = f ∘ g)
idMap      : (C : Cat) → Map C C
comp-assoc : comp h (comp g f) ≡ comp (comp h g) f  -- associativity
comp-id-l  : comp (idMap B) f ≡ f                   -- unit laws
comp-id-r  : comp f (idMap A) ≡ f
pentagonator : …                                    -- Mac Lane pentagon for the reassociator
Id-triangle2 : …                                    -- Mac Lane triangle
cat-univalence : (C : Cat) → is-contr (Equiv-from C) -- isomorphic objects are equal
𝟏c         : Cat                                    -- terminal category
terminal   : (C : Cat) → is-contr (Map C 𝟏c)
```

### Finite limits and exponentials — `Category/Pullbacks.agda`, `Category/Exponentials.agda`

```agda
pb          : Map B A → Map C A → Cat               -- pullback object
pb-pr₁ / pb-pr₂ / pb-comm : …                       -- its projections + commuting square
pb-is-equiv : is-equiv (pb-comparison f g X)        -- the pullback universal property

Fun         : Cat → Cat → Cat                       -- exponential / functor category
ev          : Map (Fun A B ×c A) B                  -- evaluation
exp-is-equiv : is-equiv (exp-comparison A B X)       -- the exponential universal property
```

### The interval `𝕀` — `Category/HigherCat.agda`, `Interval/Interval.agda`

```agda
𝕀           : Cat                                   -- the interval (the "walking arrow")
𝕀-ob        : Ob 𝕀 ≃ 𝟚                              -- it has exactly two objects
𝕀-mor-order : pr₁ 𝕀-ob (dom g) ≤𝟚 pr₁ 𝕀-ob (cod g)  -- morphisms respect 0 ≤ 1
𝕀-char-inverse : Monotone C → Map C 𝕀               -- 𝕀 classifies monotone maps:
𝕀-char-rinv / 𝕀-char-linv : …                       --   Map C 𝕀 ≃ Monotone C
```

### Segal axiom and simplices — `Simplices/Segal.agda`, `Simplices/SegalGeom.agda`

```agda
d₀₁ d₁₂ d₀₂ : Mor (Δ 2)                             -- the three edges of Δ²
segal-comm / d₀₂-start / d₀₂-end : …                -- they form a composable triangle
segal-is-equiv : is-equiv (segal-comparison C)       -- the Segal / Rezk condition
𝕀-hom-contr : is-contr (Hom 𝕀 𝕀₀ 𝕀₁)                -- 𝕀 has a unique nontrivial arrow
segal-coface-01 : d₀₁ ≡ comp (face 1) eval-pt-inv    -- the d₀₁/d₁₂ edges are the
segal-coface-12 : d₁₂ ≡ comp (lastedge 1) eval-pt-inv --   expected geometric cofaces
```

There are **no** proof-debt postulates: in particular the base case
`S-pushout zero = base-Sq1` holds directly, with no work-around postulate, and
everything in `Posetal/`, `Squares/`, and `Solvers/` is postulate-free.

## Layout

`Pushout.agda` (the entry point with the main theorem) sits at the root; the 45
supporting modules are grouped into layer subdirectories:

| Directory       | Contents |
|-----------------|----------|
| `Foundations/`  | HoTT base: `Spartan` (funext, univalence), `HLevels`, `SigmaEquiv`, `Retracts`, `Coherence`. |
| `Category/`     | Ambient category & exponentials: `CatAxioms`, `HigherCat`, `Constructions`, `Pullbacks`, `Exponentials`, `ExpEval`, `UnitIso`, `Product`. |
| `Solvers/`      | Path-algebra automation: `GroupoidSolver`, `CayleyAssoc`, `Normaliser`, `PastingDSL`, `PastingTest`. |
| `Interval/`     | The interval `𝕀`, order combinatorics and faces: `Interval`, `IntervalPosetal`, `OrdCompare`, `OrdComb`, `FaceOrd`, `FaceOrdCompat`. |
| `Posetal/`      | Posetal structure of the simplices: `PosetalCore`, `FunIPosetal`, `Posetal`. |
| `Simplices/`    | Simplices and the Segal axiom: `Segal`, `SegalGeom`, `FaceMap`, `FaceTop`, `FaceTopProof`, `LastEdge`, `SimplexRetract`, `SimplexRetractValues`. |
| `Squares/`      | Pushout-square algebra and the gluing square: `Square`, `SquareAlg`, `SquareGeom`, `ConeUnit`, `ConeComp`, `ConeNat`, `TimesI`, `PushoutBase`, `PushoutDef`, `PushoutProof`. |
