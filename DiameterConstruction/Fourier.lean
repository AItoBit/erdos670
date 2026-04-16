/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import Mathlib
import DiameterConstruction.Defs

/-!
# Fourier identities for the Erdos counterexample profile

This file establishes the Fourier-series identities that connect the explicit coefficients
from the paper to the profile function `H`:

* the classical identity
  `∑ (1 - cos (n θ)) / n^2 = π θ / 2 - θ^2 / 4` on `[0, 2π]`,
* its odd-frequency part
  `∑ (1 - cos ((2k+1) θ)) / (2k+1)^2 = π θ / 4` on `[0, π]`,
* and the perturbed odd series whose sum is exactly `H`.
-/

namespace DiameterConstruction

open scoped Real Topology
open Real Set

noncomputable section

/-- The perturbed odd coefficients from the paper:
`c₁ = 7/8`, and `c_{2k+1} = 1 / (2k+1)^2` for higher odd frequencies. -/
def perturbedOddCoeff (k : ℕ) : ℝ :=
  if k = 0 then (7 : ℝ) / 8 else 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

@[simp] lemma perturbedOddCoeff_zero : perturbedOddCoeff 0 = (7 : ℝ) / 8 := by
  simp [perturbedOddCoeff]

lemma perturbedOddCoeff_pos (k : ℕ) : 0 < perturbedOddCoeff k := by
  by_cases hk : k = 0
  · simp [perturbedOddCoeff, hk]
  · simp [perturbedOddCoeff, hk]
    positivity

lemma cos_inv_sq_hasSum_explicit {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * x))
      (π ^ 2 * (x ^ 2 - x + (1 : ℝ) / 6)) := by
  convert (hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx) using 1
  have hcoeff :
      ((-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)) = π ^ 2 := by
    norm_num
    ring
  rw [hcoeff]
  change π ^ 2 * (x ^ 2 - x + (1 : ℝ) / 6) = π ^ 2 * bernoulliFun 2 x
  rw [bernoulliFun_two]
  ring

/-- The classical cosine-series identity
`∑ (1 - cos(n θ)) / n^2 = π θ / 2 - θ^2 / 4` on `[0, 2π]`. -/
lemma hasSum_one_sub_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ)))
      (π * θ / 2 - θ ^ 2 / 4) := by
  have htwo_pi_pos : 0 < 2 * π := by positivity
  have hx : θ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hθ.1 (le_of_lt htwo_pi_pos)
    · exact (div_le_iff₀ htwo_pi_pos).2 (by nlinarith [hθ.2])
  have hcos := cos_inv_sq_hasSum_explicit hx
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have hsub :
      HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 - (1 / (n : ℝ) ^ 2 * Real.cos (n * θ)))
        (π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6)) := by
    exact hzeta.sub (hcos.congr_fun fun n => by
      have harg : 2 * π * (n : ℝ) * (θ / (2 * π)) = (n : ℝ) * θ := by
        field_simp [Real.pi_ne_zero]
      simp [harg])
  have hsub' :
      HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ)))
        (π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6)) := by
    exact hsub.congr_fun (fun n => by ring)
  have hrhs : π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6) =
      π * θ / 2 - θ ^ 2 / 4 := by
    field_simp [Real.pi_ne_zero]
    ring
  exact hrhs ▸ hsub'

/-- The odd-frequency part of the previous identity:
`∑ (1 - cos((2k+1)θ)) / (2k+1)^2 = π θ / 4` on `[0, π]`. -/
lemma hasSum_odd_one_sub_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    HasSum (fun k : ℕ => (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) * (1 - Real.cos ((2 * k + 1) * θ)))
      (π * θ / 4) := by
  let f : ℕ → ℝ := fun n => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ))
  have hall : HasSum f (π * θ / 2 - θ ^ 2 / 4) := by
    simpa [f] using hasSum_one_sub_cos_div_sq (θ := θ) (by
      refine ⟨hθ.1, ?_⟩
      nlinarith [hθ.2, Real.pi_pos])
  have hdouble : HasSum (fun k : ℕ => (1 / 4 : ℝ) * ((1 / (k : ℝ) ^ 2) * (1 - Real.cos (k * (2 * θ)))))
      ((π * θ - θ ^ 2) / 4) := by
    have h2θ : 2 * θ ∈ Set.Icc (0 : ℝ) (2 * π) := by
      constructor
      · nlinarith [hθ.1]
      · nlinarith [hθ.2]
    have hdouble0 :
        HasSum (fun k : ℕ => (1 / 4 : ℝ) * ((1 / (k : ℝ) ^ 2) * (1 - Real.cos (k * (2 * θ)))))
          ((1 / 4 : ℝ) * (π * (2 * θ) / 2 - (2 * θ) ^ 2 / 4)) :=
      (hasSum_one_sub_cos_div_sq (θ := 2 * θ) h2θ).mul_left (1 / 4 : ℝ)
    convert hdouble0 using 1
    ring
  have heven : HasSum (fun k : ℕ => f (2 * k))
      ((π * θ - θ ^ 2) / 4) := by
    convert hdouble using 1
    · funext k
      simp [f]
      ring_nf
  have hsodd : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have hs0 : Summable ((fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ∘ fun k : ℕ => 2 * k + 1) := by
      exact hasSum_zeta_two.summable.comp_injective (fun a b h => by omega)
    have hs : Summable (fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa [Function.comp_def] using hs0
    refine (hs.mul_left 2).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
    · have hcos : 1 - Real.cos ((2 * k + 1) * θ) ≤ 2 := by
        nlinarith [Real.neg_one_le_cos ((2 * k + 1) * θ)]
      calc
        f (2 * k + 1)
            = (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * (1 - Real.cos ((2 * k + 1) * θ)) := by
                simp [f]
        _ ≤ (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * 2 := by gcongr
        _ = 2 * (1 / ((((2 * k + 1 : ℕ) : ℝ)) ^ 2)) := by
          ring
  have htsum := tsum_even_add_odd (f := f) heven.summable hsodd
  have hodd_tsum : ∑' k : ℕ, f (2 * k + 1) = π * θ / 4 := by
    rw [hall.tsum_eq, heven.tsum_eq] at htsum
    linarith
  convert (hsodd.hasSum_iff.mpr hodd_tsum) using 1 with k
  simp [f]

/-- The perturbed odd series from the paper sums to the explicit profile `H`. -/
lemma hasSum_perturbedOddCoeff_profile {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    HasSum (fun k : ℕ => perturbedOddCoeff k * (1 - Real.cos ((2 * k + 1) * θ))) (H θ) := by
  have hodd := hasSum_odd_one_sub_cos_div_sq hθ
  have h0 :
      (1 / ((2 * 0 + 1 : ℕ) : ℝ) ^ 2) * (1 - Real.cos ((2 * 0 + 1) * θ)) =
        1 - Real.cos θ := by
    norm_num
  convert hodd.update 0 ((7 : ℝ) / 8 * (1 - Real.cos θ)) using 1
  · funext k
    by_cases hk : k = 0
    · subst hk
      simp [perturbedOddCoeff]
    · simp [perturbedOddCoeff, hk]
  · norm_num
    unfold H
    ring

/-- A `tsum` version of the previous identity. -/
theorem H_eq_tsum_perturbedOddCoeff {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    H θ = ∑' k : ℕ, perturbedOddCoeff k * (1 - Real.cos ((2 * k + 1) * θ)) :=
  (hasSum_perturbedOddCoeff_profile hθ).tsum_eq.symm

end

end DiameterConstruction

