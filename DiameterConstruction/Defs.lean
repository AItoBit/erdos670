/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic

/-!
# Counterexample to a dimension-free diameter conjecture of Erdos - Definitions

This file introduces the basic scalar-valued objects used throughout the formalization:
the squared distance profile `H`, the distance profile `G = sqrt o H`, and the asymptotic
constant `cStar = 1 - 1 / pi^2`.

## Main definitions

* `DiameterConstruction.H` : the squared distance profile.
* `DiameterConstruction.G` : the distance profile.
* `DiameterConstruction.cStar` : the asymptotic constant.

## References

* "A counterexample to a dimension-free diameter conjecture of Erdos"
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace DiameterConstruction

open Real

noncomputable section

/-- The squared distance profile function `H(θ) = πθ/4 - (1 - cos θ)/8`.

This arises as the squared distance between points at angular separation `θ` in a
weighted product of regular polygons, after applying a one-frequency perturbation
to the identity Fourier series `∑ (1 - cos jθ)/j²`. -/
def H (θ : ℝ) : ℝ := π * θ / 4 - (1 - cos θ) / 8

/-- The distance profile function `G(θ) = √(H(θ))`.

The pairwise distances in the construction are given by `G(2πs/m)` for
`s = 1, …, N`. The key properties are that `G` is strictly increasing and
strictly concave on `(0, π)`. -/
def G (θ : ℝ) : ℝ := sqrt (H θ)

/-- The asymptotic constant `c* = 1 - 1/π² ≈ 0.8987`.

This is the ratio `diam(𝒳ₘ)/m` in the limit, which is strictly less than `1`,
disproving the dimension-free form of Erdős's conjecture. -/
def cStar : ℝ := 1 - 1 / π ^ 2

/-- The first derivative of `H`: `H'(θ) = π/4 - sin(θ)/8`. -/
def H' (θ : ℝ) : ℝ := π / 4 - sin θ / 8

/-- The second derivative of `H`: `H''(θ) = -cos(θ)/8`. -/
def H'' (θ : ℝ) : ℝ := -(cos θ) / 8

/-- The first derivative of `G`: `G'(θ) = H'(θ) / (2√(H(θ)))`. -/
def G' (θ : ℝ) : ℝ := H' θ / (2 * sqrt (H θ))

/-- The numerator of `G''(θ)`, equal to `2H(θ)H''(θ) - H'(θ)²`. -/
def G''_num (θ : ℝ) : ℝ := 2 * H θ * H'' θ - H' θ ^ 2

end

end DiameterConstruction

