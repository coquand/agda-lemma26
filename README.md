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

The development is postulate-free except for its **admissible axioms**, which
are the intended categorical/HoTT input, not gaps in the proof:

- **Foundations** — `Spartan.agda` (function extensionality, univalence),
  `CatAxioms.agda` (the ambient wild category: composition, associativity,
  units, coherence), `HigherCat.agda` (the interval `𝕀`), `Exponentials.agda`,
  `Pullbacks.agda`.
- **The interval / simplices** — `Interval.agda` (characterization of `𝕀`),
  `Segal.agda` and `SegalGeom.agda` (the geometric **Segal axiom**, i.e.
  `d₀₁`/`d₁₂`/`segal-is-equiv`/`segal-coface`).

There are **no** proof-debt postulates: in particular the base case
`S-pushout zero = base-Sq1` holds directly, with no work-around postulate.

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
