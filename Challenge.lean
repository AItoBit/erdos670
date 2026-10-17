/-
Copyright 2026 The Formal Conjectures Authors.
Released under the MIT license, as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Ho's counterexample to the dimension-uniform form of Erdős problem 670

Boon Suan Ho constructs infinitely many finite Euclidean point sets with all
distances between distinct unordered pairs separated by at least one. Their
diameters are at most $(1-1/\pi^2+\varepsilon)n^2$ for every positive
$\varepsilon$, with ambient dimension $n^2-n$. Consequently the asymptotic
lower bound $(1-\varepsilon)n^2$ cannot hold uniformly over dimensions.

This records the result of https://arxiv.org/abs/2604.15305v1, not a new
mathematical proof. The underlying formal proof is included in the
`DiameterConstruction` modules. The formulation agrees with the `ho` and
`uniform_in_dim` variants of Erdős problem 670 in Formal Conjectures.
The conjecture with each dimension fixed before the asymptotic limit remains
open, as stated in Remark 9 of Ho's paper.
-/

public section

namespace Erdos670

open Filter

/-- Distances of different unordered pairs of distinct points are at least one apart. -/
@[expose] def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/-- For every $\varepsilon>0$, infinitely many $n$ admit $n$ points in
$\mathbb R^{n^2-n}$ with separated distances and diameter at most
$(1-1/\pi^2+\varepsilon)n^2$. -/
theorem erdos_670.variants.ho :
    ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin (n ^ 2 - n))), A.card = n ∧
        HasSeparatedDistances A ∧
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin (n ^ 2 - n)))) ≤
          (1 - 1 / Real.pi ^ 2 + ε) * (n : ℝ) ^ 2 := by sorry

/-- The asymptotic diameter lower bound $(1-\varepsilon)n^2$ for sets with
separated distances does not hold uniformly over all ambient dimensions. -/
theorem erdos_670.variants.uniform_in_dim :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) :=
  by sorry

end Erdos670
