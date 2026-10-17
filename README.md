# DiameterConstruction

This repository contains a Lean 4 / mathlib formalization of the main mathematical content of
the paper
["Erdős's diameter conjecture for separated distances fails in high dimensions"](https://arxiv.org/abs/2604.15305).

## Main result

The formalization proves that there is a constant

`cStar = 1 - 1 / pi^2 < 1`

and an error term `eps(q) -> 0` such that for infinitely many `n = q + 1` there exists an
`n`-point set `X ⊂ R^(n^2 - n)` with the following properties:

- whenever `{x, y}` and `{u, v}` are distinct unordered pairs from `X`, their distances differ
  by at least `1`, i.e.
  `|dist(x, y) - dist(u, v)| >= 1`
- `diam(X) <= (cStar + eps(q)) * n^2`

Equivalently, the construction produces infinitely many point sets whose distinct pairwise
distances are mutually `1`-separated, while the diameter is asymptotically

`(1 - 1 / pi^2 + o(1)) * n^2`.

This disproves the dimension-free diameter lower bound conjectured in the paper.

## Status

- The complete proof dependency closure compiles with warnings as errors using
  `python verify.py`. Principal theorem axioms were inspected with Lean 4.28.0.
- No `sorry`s remain in the formalization.
- The development includes the Singer difference-set input, the Euclidean realization, the
  scaling argument, the exact finite diameter formula, and the final asymptotic theorem.

## Entry points

The most useful theorems and definitions to start from are:

- `DiameterConstruction.cStar`
  in `DiameterConstruction/Defs.lean`

  The constant `1 - 1 / pi^2`.

- `DiameterConstruction.singer_exists`
  in `DiameterConstruction/Singer.lean`

  Singer's theorem: for each prime power `q`, there is a cyclic
  `(q^2 + q + 1, q + 1, 1)` difference set.

- `DiameterConstruction.singer_realization_exists`
  in `DiameterConstruction/MainTheorem.lean`

  The concrete Euclidean realization with distance law
  `dist (p t) (p u) = G (sepAngle (t - u))`.

- `DiameterConstruction.primePower_counterexample_exactDimension_with_diam`
  in `DiameterConstruction/Scaling.lean`

  For each prime power `q`, an exact finite counterexample in ambient dimension
  `R^((q + 1)^2 - (q + 1)) = R^(n^2 - n)`, together with its exact diameter formula.

- `DiameterConstruction.primePowerDiameter_over_cardSq_tendsto_cStar`
  in `DiameterConstruction/MainTheorem.lean`

  The asymptotic diameter ratio tends to `cStar`.

- `DiameterConstruction.infinitely_many_quantitative_counterexamples`
  in `DiameterConstruction/MainTheorem.lean`

  The final infinite-family theorem in the form
  `diam(X) <= (cStar + eps(q)) * (q + 1)^2` with `eps(q) -> 0`.

## File guide

- `DiameterConstruction.lean`

  Umbrella import for the whole development.

- `DiameterConstruction/Defs.lean`

  Basic definitions: the profile functions `H`, `G`, and the constant `cStar`.

- `DiameterConstruction/Analysis.lean`

  Analytic properties of `H` and `G`, including strict monotonicity and strict concavity of `G`
  on `[0, pi]`.

- `DiameterConstruction/Fourier.lean`

  Fourier identities that connect the explicit coefficient sequence from the paper to the profile
  function `H`.

- `DiameterConstruction/Singer.lean`

  The finite-field proof of Singer's theorem and transport back to `ZMod`.

- `DiameterConstruction/Construction.lean`

  Combinatorial consequences of Singer difference sets: unordered pairs are controlled by their
  cyclic separation.

- `DiameterConstruction/Profile.lean`

  The cyclic separation angle `sepAngle` and the resulting profile injectivity statements.

- `DiameterConstruction/Realization.lean`

  Weighted polygon realizations in Euclidean space and their exact squared-distance formulas.

- `DiameterConstruction/DiscreteProfile.lean`

  The specific Fourier weight family from the paper and the exact identity
  `dist = G (sepAngle (t - u))` on the cyclic samples.

- `DiameterConstruction/Scaling.lean`

  Scaling by the smallest distance gap, exact finite counterexamples, and exact diameter.

- `DiameterConstruction/MainTheorem.lean`

  The asymptotic limit theorems and the final infinite-family counterexample statements.

## Build

This project targets Lean `v4.28.0` with mathlib `v4.28.0`.

```bash
lake build
```

To load the full development in Lean:

```lean
import DiameterConstruction
```

## Axioms

The development uses only the standard classical axioms already present in mathlib:
`propext`, `Classical.choice`, and `Quot.sound`.

## Formal Conjectures bridge

`DiameterConstruction/RepositoryBridge.lean` states the growing-dimension
counterexample using exactly the finite-set definition and quantifiers of
`Erdos670.erdos_670.variants.ho` in Formal Conjectures. It derives
`Erdos670.erdos_670.variants.uniform_in_dim` from that result.

The original construction and its proof are Boon Suan Ho's work. This addition
converts the formulation; it does not solve the fixed-dimension conjecture.
Broad Mathlib imports were narrowed for memory use. One projective-subspace
coercion uses its carrier explicitly. No theorem statements were changed.

```bash
lake --wfail build DiameterConstruction.RepositoryBridge
lake env lean Verification.lean
```

`Verification.lean` prints the bridge statements and the axiom dependencies of
the principal imported and bridge theorems.

The standard Lake build was attempted on an 8 GB Windows host but not completed
because of its memory and metadata costs. Direct Lean compilation of every
module succeeded. Run `python verify.py` for the sequential verification used
here; it saves compiler commands, results and source hashes locally.
