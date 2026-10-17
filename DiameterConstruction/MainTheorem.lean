/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
module

public import DiameterConstruction.Analysis
public import DiameterConstruction.DiscreteProfile
public import DiameterConstruction.Scaling
public import DiameterConstruction.Singer
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Prime.Infinite

/-!
# Main theorem - A counterexample to Erdos's dimension-free diameter conjecture

Erdos conjectured that every `n`-point set in Euclidean space whose pairwise distances are
mutually at least `1` apart must have diameter at least `(1 + o(1)) * n^2`, independently
of the ambient dimension. This file packages the final asymptotic statements proved by the
construction developed in the earlier files.

The construction combines:
1. A Singer difference set `D ⊂ ZMod m` with `m = q^2 + q + 1` and `|D| = q + 1 = n`.
2. A weighted product of regular `m`-gons whose distance profile is `G (2 * pi * s / m)`.
3. The strict concavity of `G` ensures the distance gaps are decreasing, so after scaling,
   all pairwise distances are at least `1` apart.
4. The asymptotic diameter is `(1 - 1 / pi^2 + o(1)) * n^2`, contradicting the conjecture.

## Main results

* `DiameterConstruction.primePowerDiameter_over_order_tendsto_cStar`
* `DiameterConstruction.primePowerDiameter_over_cardSq_tendsto_cStar`
* `DiameterConstruction.infinitely_many_quantitative_counterexamples`
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace DiameterConstruction

open Real Set Filter
open scoped Topology

noncomputable section

/-! ### The asymptotic constant -/

lemma cStar_pos : 0 < cStar := by
  exact sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_gt_three ] )

lemma cStar_lt_one : cStar < 1 := by
  exact sub_lt_self _ <| by positivity;

/-! ### Asymptotic diameter (Proposition 4.1)

The ratio `G(π) / (2π · G'(π⁻))` equals `c*`. Since the diameter of the scaled
point set is `dₙ / (dₙ - dₙ₋₁)` and this ratio converges to `G(π) / (2π · G'(π⁻))`,
the asymptotic diameter is `c* · m ∼ c* · n²`. -/

lemma G_pi : G π = sqrt ((π ^ 2 - 1) / 4) := by
  exact congrArg Real.sqrt ( H_pi )

lemma H'_pi : H' π = π / 4 := by
  exact sub_eq_self.mpr ( by norm_num )

/-
The limit ratio `4·H(π)/π²` equals `c* = 1 - 1/π²`.

This is the key asymptotic identity: by the mean value theorem, the diameter of the
scaled construction satisfies `diam(𝒳ₘ)/m → G(π)/(2π·G'(π⁻)) = 4H(π)/π² = c*`.
-/
lemma diameter_ratio_eq_cStar :
    4 * H π / π ^ 2 = cStar := by
      rw [ H_pi ] ; ring_nf;
      unfold cStar;
      norm_num

def primePowerOrder (q : Nat) : Nat := q ^ 2 + q + 1

instance primePowerOrder_neZero (q : Nat) : NeZero (primePowerOrder q) := by
  refine ⟨by
    unfold primePowerOrder
    omega⟩

/-- The exact finite diameter of the scaled construction for the parameter `q`,
before rewriting it in asymptotic form. -/
def primePowerDiameter (q : Nat) : Real :=
  scaleFactor (m := primePowerOrder q) * gridDist (m := primePowerOrder q) (primePowerOrder q / 2)

/-- The top grid angle `theta_N = 2 * pi * N / m` with `N = floor(m / 2)`. -/
def topGapAngle (q : Nat) : Real :=
  2 * Real.pi * (((primePowerOrder q) / 2 : Nat) : Real) / primePowerOrder q

/-- The penultimate grid angle `theta_(N-1)`. -/
def prevTopGapAngle (q : Nat) : Real :=
  2 * Real.pi * ((((primePowerOrder q) / 2 - 1 : Nat)) : Real) / primePowerOrder q

lemma primePowerOrder_half_ge_two {q : Nat} (hq : 2 <= q) :
    2 <= primePowerOrder q / 2 := by
  unfold primePowerOrder
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq hq
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)

lemma topGapAngle_mem_Icc (q : Nat) : topGapAngle q ∈ Icc 0 π := by
  simpa [topGapAngle] using
    gridAngle_mem_Icc (m := primePowerOrder q)
      (s := primePowerOrder q / 2)
      (le_rfl : primePowerOrder q / 2 <= primePowerOrder q / 2)

lemma prevTopGapAngle_mem_Icc (q : Nat) (_hq : 2 <= q) :
    prevTopGapAngle q ∈ Icc 0 π := by
  have hs : primePowerOrder q / 2 - 1 <= primePowerOrder q / 2 := by
    omega
  simpa [prevTopGapAngle] using
    gridAngle_mem_Icc (m := primePowerOrder q)
      (s := primePowerOrder q / 2 - 1) hs

lemma prevTopGapAngle_lt_topGapAngle (q : Nat) (hq : 2 <= q) :
    prevTopGapAngle q < topGapAngle q := by
  simpa [prevTopGapAngle, topGapAngle] using
    gridAngle_strictMono (m := primePowerOrder q)
      (s := primePowerOrder q / 2 - 1)
      (t := primePowerOrder q / 2)
      (le_rfl : primePowerOrder q / 2 <= primePowerOrder q / 2)
      (by
        have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
        omega)

lemma topGapAngle_eq (q : Nat) :
    topGapAngle q = π - π / primePowerOrder q := by
  have hdouble_nat : 2 * (primePowerOrder q / 2) = primePowerOrder q - 1 := by
    unfold primePowerOrder
    rw [Nat.mul_comm]
    simpa using primePower_reindexed_dim q
  have hdouble :
      (2 : Real) * (((primePowerOrder q / 2 : Nat) : Real)) = ((primePowerOrder q - 1 : Nat) : Real) := by
    exact_mod_cast hdouble_nat
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hm1 : (((primePowerOrder q - 1 : Nat) : Real)) = (primePowerOrder q : Real) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (primePowerOrder_neZero q).ne))]
    norm_num
  calc
    topGapAngle q = π * ((2 : Real) * (((primePowerOrder q / 2 : Nat) : Real)) / primePowerOrder q) := by
      unfold topGapAngle
      ring
    _ = π * (((primePowerOrder q - 1 : Nat) : Real) / primePowerOrder q) := by rw [hdouble]
    _ = π - π / primePowerOrder q := by
      rw [hm1]
      field_simp [hm0]

lemma prevTopGapAngle_eq (q : Nat) (hq : 2 <= q) :
    prevTopGapAngle q = π - 3 * π / primePowerOrder q := by
  have hdouble_prev_nat : 2 * (primePowerOrder q / 2 - 1) = primePowerOrder q - 3 := by
    have hdouble_nat : 2 * (primePowerOrder q / 2) = primePowerOrder q - 1 := by
      unfold primePowerOrder
      rw [Nat.mul_comm]
      simpa using primePower_reindexed_dim q
    omega
  have hdouble_prev :
      (2 : Real) * (((primePowerOrder q / 2 - 1 : Nat) : Real)) = ((primePowerOrder q - 3 : Nat) : Real) := by
    exact_mod_cast hdouble_prev_nat
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hm3nat : 3 <= primePowerOrder q := by
    unfold primePowerOrder
    omega
  have hm3 : (((primePowerOrder q - 3 : Nat) : Real)) = (primePowerOrder q : Real) - 3 := by
    rw [Nat.cast_sub hm3nat]
    norm_num
  calc
    prevTopGapAngle q =
        π * ((2 : Real) * (((primePowerOrder q / 2 - 1 : Nat) : Real)) / primePowerOrder q) := by
          unfold prevTopGapAngle
          ring
    _ = π * (((primePowerOrder q - 3 : Nat) : Real) / primePowerOrder q) := by rw [hdouble_prev]
    _ = π - 3 * π / primePowerOrder q := by
          rw [hm3]
          field_simp [hm0]

lemma G'_pi : G' π = π / (8 * G π) := by
  unfold G'
  rw [H'_pi]
  rw [G]
  ring_nf

lemma continuousAt_G'_pi : ContinuousAt G' π := by
  unfold G'
  refine ContinuousAt.div ?_ ?_ ?_
  · exact (hasDerivAt_H' π).continuousAt
  · exact ContinuousAt.mul continuousAt_const (continuous_H.continuousAt.sqrt)
  · have hHpi : 0 < H π := H_pos Real.pi_pos le_rfl
    exact mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.2 hHpi)

lemma diameter_ratio_limit_value_eq_cStar :
    G π / (2 * π * G' π) = cStar := by
  have hGne : G π ≠ 0 := G_ne_zero Real.pi_pos le_rfl
  calc
    G π / (2 * π * G' π) = 4 * G π ^ 2 / π ^ 2 := by
      rw [G'_pi]
      field_simp [hGne, Real.pi_ne_zero]
      ring
    _ = 4 * H π / π ^ 2 := by rw [G_sq Real.pi_pos.le le_rfl]
    _ = cStar := diameter_ratio_eq_cStar

lemma continuous_G : Continuous G := by
  simpa [G] using Continuous.sqrt continuous_H

lemma lastGap_eq_topGap_difference (q : Nat) (hq : 2 <= q) :
    lastGap (m := primePowerOrder q) = G (topGapAngle q) - G (prevTopGapAngle q) := by
  have hsucc : primePowerOrder q / 2 - 1 + 1 = primePowerOrder q / 2 := by
    have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
    omega
  simp [lastGap, gridGap, gridDist, topGapAngle, prevTopGapAngle, hsucc]

lemma exists_topGap_mvt_point (q : Nat) (hq : 2 <= q) :
    ∃ ξ ∈ Ioo (prevTopGapAngle q) (topGapAngle q),
      G' ξ = (G (topGapAngle q) - G (prevTopGapAngle q)) / (topGapAngle q - prevTopGapAngle q) := by
  have hab : prevTopGapAngle q < topGapAngle q := prevTopGapAngle_lt_topGapAngle q hq
  refine exists_hasDerivAt_eq_slope G G' hab ?_ ?_
  · refine continuousOn_G.mono ?_
    exact Icc_subset_Icc (prevTopGapAngle_mem_Icc q hq).1 (topGapAngle_mem_Icc q).2
  · intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt (prevTopGapAngle_mem_Icc q hq).1 hx.1
    have hxpi : x <= π := le_trans hx.2.le (topGapAngle_mem_Icc q).2
    exact hasDerivAt_G hx0 hxpi

noncomputable def topGapMVTPoint (q : Nat) : Real :=
  if hq : 2 <= q then
    Classical.choose (exists_topGap_mvt_point q hq)
  else
    π

lemma topGapMVTPoint_mem_Ioo (q : Nat) (hq : 2 <= q) :
    topGapMVTPoint q ∈ Ioo (prevTopGapAngle q) (topGapAngle q) := by
  simpa [topGapMVTPoint, hq] using (Classical.choose_spec (exists_topGap_mvt_point q hq)).1

lemma topGapMVTPoint_eq_slope (q : Nat) (hq : 2 <= q) :
    G' (topGapMVTPoint q) =
      (G (topGapAngle q) - G (prevTopGapAngle q)) / (topGapAngle q - prevTopGapAngle q) := by
  simpa [topGapMVTPoint, hq] using (Classical.choose_spec (exists_topGap_mvt_point q hq)).2

lemma topGapAngle_sub_prevTopGapAngle (q : Nat) (hq : 2 <= q) :
    topGapAngle q - prevTopGapAngle q = 2 * π / primePowerOrder q := by
  rw [topGapAngle_eq q, prevTopGapAngle_eq q hq]
  ring

lemma primePowerOrder_tendsto_atTop :
    Tendsto (fun q : Nat => (primePowerOrder q : Real)) atTop atTop := by
  refine tendsto_atTop_mono (fun q => ?_) tendsto_natCast_atTop_atTop
  have hquad : (q : Real) <= (q : Real) ^ 2 + q + 1 := by
    nlinarith [sq_nonneg (q : Real)]
  simpa [primePowerOrder] using hquad

lemma topGapAngle_tendsto_pi :
    Tendsto topGapAngle atTop (𝓝 π) := by
  have hdiv : Tendsto (fun q : Nat => π / (primePowerOrder q : Real)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop primePowerOrder_tendsto_atTop
  have heq : topGapAngle = fun q : Nat => π - π / (primePowerOrder q : Real) := by
    funext q
    exact topGapAngle_eq q
  rw [heq]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => π) atTop (𝓝 π)).sub hdiv)

lemma prevTopGapAngle_tendsto_pi :
    Tendsto prevTopGapAngle atTop (𝓝 π) := by
  have hdiv : Tendsto (fun q : Nat => 3 * π / (primePowerOrder q : Real)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop primePowerOrder_tendsto_atTop
  have hmain :
      Tendsto (fun q : Nat => π - 3 * π / (primePowerOrder q : Real)) atTop (𝓝 π) :=
    by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : Nat => π) atTop (𝓝 π)).sub hdiv)
  have heq :
      prevTopGapAngle =ᶠ[atTop] fun q : Nat => π - 3 * π / (primePowerOrder q : Real) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    rw [prevTopGapAngle_eq q hq]
  exact hmain.congr' heq.symm

lemma topGapMVTPoint_tendsto_pi :
    Tendsto topGapMVTPoint atTop (𝓝 π) := by
  have hlow : ∀ᶠ q in atTop, prevTopGapAngle q <= topGapMVTPoint q := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    exact (topGapMVTPoint_mem_Ioo q hq).1.le
  have hhigh : ∀ᶠ q in atTop, topGapMVTPoint q <= topGapAngle q := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    exact (topGapMVTPoint_mem_Ioo q hq).2.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    prevTopGapAngle_tendsto_pi topGapAngle_tendsto_pi hlow hhigh

lemma G'_topGapMVTPoint_tendsto_pi :
    Tendsto (fun q : Nat => G' (topGapMVTPoint q)) atTop (𝓝 (G' π)) := by
  exact continuousAt_G'_pi.tendsto.comp topGapMVTPoint_tendsto_pi

lemma primePowerDiameter_ratio_eq_mvt (q : Nat) (hq : 2 <= q) :
    primePowerDiameter q / (primePowerOrder q : Real) =
      G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)) := by
  have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hlast_ne : lastGap (m := primePowerOrder q) ≠ 0 := (lastGap_pos (m := primePowerOrder q) hN).ne'
  have hgrid : gridDist (m := primePowerOrder q) (primePowerOrder q / 2) = G (topGapAngle q) := by
    rfl
  have hlast :
      lastGap (m := primePowerOrder q) =
        (2 * π / primePowerOrder q) * G' (topGapMVTPoint q) := by
    calc
      lastGap (m := primePowerOrder q) = G (topGapAngle q) - G (prevTopGapAngle q) :=
        lastGap_eq_topGap_difference q hq
      _ = (topGapAngle q - prevTopGapAngle q) * G' (topGapMVTPoint q) := by
        have hstep_ne : topGapAngle q - prevTopGapAngle q ≠ 0 := by
          exact sub_ne_zero.mpr (prevTopGapAngle_lt_topGapAngle q hq).ne'
        rw [topGapMVTPoint_eq_slope q hq]
        field_simp [hstep_ne]
      _ = (2 * π / primePowerOrder q) * G' (topGapMVTPoint q) := by
        rw [topGapAngle_sub_prevTopGapAngle q hq]
  calc
    primePowerDiameter q / (primePowerOrder q : Real) =
        (scaleFactor (m := primePowerOrder q) *
          gridDist (m := primePowerOrder q) (primePowerOrder q / 2)) / (primePowerOrder q : Real) := by
          rfl
    _ = gridDist (m := primePowerOrder q) (primePowerOrder q / 2) /
          ((primePowerOrder q : Real) * lastGap (m := primePowerOrder q)) := by
            unfold scaleFactor
            field_simp [hlast_ne, hm0]
    _ = G (topGapAngle q) /
          ((primePowerOrder q : Real) *
            ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q))) := by
              rw [hgrid, hlast]
    _ = G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)) := by
          have hm_mul : (primePowerOrder q : Real) * (2 * π / primePowerOrder q) = 2 * π := by
            field_simp [hm0]
          have hden :
              (primePowerOrder q : Real) *
                  ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q)) =
                2 * π * G' (topGapMVTPoint q) := by
            calc
              (primePowerOrder q : Real) *
                  ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q)) =
                  ((primePowerOrder q : Real) * (2 * π / primePowerOrder q)) *
                    G' (topGapMVTPoint q) := by ring
              _ = (2 * π) * G' (topGapMVTPoint q) := by rw [hm_mul]
              _ = 2 * π * G' (topGapMVTPoint q) := by ring
          rw [hden]

theorem primePowerDiameter_over_order_tendsto_cStar :
    Tendsto (fun q : Nat => primePowerDiameter q / (primePowerOrder q : Real)) atTop (𝓝 cStar) := by
  have heq :
      (fun q : Nat => primePowerDiameter q / (primePowerOrder q : Real)) =ᶠ[atTop]
        (fun q : Nat => G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q))) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    rw [primePowerDiameter_ratio_eq_mvt q hq]
  have hnum : Tendsto (fun q : Nat => G (topGapAngle q)) atTop (𝓝 (G π)) := by
    exact continuous_G.continuousAt.tendsto.comp topGapAngle_tendsto_pi
  have hden : Tendsto (fun q : Nat => 2 * π * G' (topGapMVTPoint q)) atTop (𝓝 (2 * π * G' π)) := by
    exact tendsto_const_nhds.mul G'_topGapMVTPoint_tendsto_pi
  have hG'pi_ne : G' π ≠ 0 := by
    have hGne : G π ≠ 0 := G_ne_zero Real.pi_pos le_rfl
    rw [G'_pi]
    exact div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hGne)
  have hden_ne : 2 * π * G' π ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hG'pi_ne
  have hratio :
      Tendsto (fun q : Nat => G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)))
        atTop (𝓝 (G π / (2 * π * G' π))) := by
    exact Tendsto.div hnum hden hden_ne
  simpa [diameter_ratio_limit_value_eq_cStar] using hratio.congr' heq.symm

lemma primePowerOrder_over_cardSq_tendsto_one :
    Tendsto (fun q : Nat => (primePowerOrder q : Real) / (q + 1) ^ 2) atTop (𝓝 1) := by
  have hrecip : Tendsto (fun q : Nat => (1 : Real) / (q + 1 : Real)) atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun q : Nat => (1 : Real) / (q + 1 : Real)) atTop (𝓝 0))
  have hbase :
      Tendsto (fun q : Nat => (1 : Real) - (1 : Real) / (q + 1 : Real)) atTop (𝓝 (1 - 0)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1)).sub hrecip
  have heqquot :
      (fun q : Nat => (q : Real) / (q + 1 : Real)) =ᶠ[atTop]
        fun q : Nat => (1 : Real) - (1 : Real) / (q + 1 : Real) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1 : (q + 1 : Real) ≠ 0 := by positivity
    field_simp [hq1]
    ring
  have hquot :
      Tendsto (fun q : Nat => (q : Real) / (q + 1 : Real)) atTop (𝓝 1) := by
    simpa using hbase.congr' heqquot.symm
  have hprod :
      Tendsto
        (fun q : Nat =>
          ((q : Real) / (q + 1 : Real)) * ((1 : Real) / (q + 1 : Real)))
        atTop (𝓝 (1 * 0)) := by
    exact hquot.mul hrecip
  have heqsmall :
      (fun q : Nat => (q : Real) / (q + 1 : Real) ^ 2) =ᶠ[atTop]
        fun q : Nat => ((q : Real) / (q + 1 : Real)) * ((1 : Real) / (q + 1 : Real)) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1 : (q + 1 : Real) ≠ 0 := by positivity
    field_simp [hq1]
  have hsmall :
      Tendsto (fun q : Nat => (q : Real) / (q + 1 : Real) ^ 2) atTop (𝓝 0) := by
    simpa using hprod.congr' heqsmall.symm
  have hmain :
      Tendsto
        (fun q : Nat => (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2)
        atTop (𝓝 (1 - 0)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1)).sub hsmall
  have heq :
      (fun q : Nat => (primePowerOrder q : Real) / (q + 1) ^ 2) =ᶠ[atTop]
        fun q : Nat => (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1sq : ((q + 1 : Real) ^ 2) ≠ 0 := by positivity
    calc
      (primePowerOrder q : Real) / (q + 1) ^ 2 =
          (((q : Real) ^ 2 + q + 1) / (q + 1 : Real) ^ 2) := by
            norm_num [primePowerOrder]
      _ = (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2 := by
            field_simp [hq1sq]
            ring
  simpa using hmain.congr' heq.symm

theorem primePowerDiameter_over_cardSq_tendsto_cStar :
    Tendsto (fun q : Nat => primePowerDiameter q / (q + 1) ^ 2) atTop (𝓝 cStar) := by
  have heq :
      (fun q : Nat => primePowerDiameter q / (q + 1) ^ 2) =ᶠ[atTop]
        (fun q : Nat =>
          (primePowerDiameter q / (primePowerOrder q : Real)) *
            ((primePowerOrder q : Real) / (q + 1) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hm0 : (primePowerOrder q : Real) ≠ 0 := by
      exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
    field_simp [hm0]
  have hmul :
      Tendsto
        (fun q : Nat =>
          (primePowerDiameter q / (primePowerOrder q : Real)) *
            ((primePowerOrder q : Real) / (q + 1) ^ 2))
        atTop (𝓝 (cStar * 1)) := by
    exact primePowerDiameter_over_order_tendsto_cStar.mul primePowerOrder_over_cardSq_tendsto_one
  simpa using hmul.congr' heq.symm

def primePowerDiameterError (q : Nat) : Real :=
  primePowerDiameter q / (q + 1) ^ 2 - cStar

lemma primePowerDiameterError_tendsto_zero :
    Tendsto primePowerDiameterError atTop (𝓝 0) := by
  simpa [primePowerDiameterError] using
    (primePowerDiameter_over_cardSq_tendsto_cStar.sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => cStar) atTop (𝓝 cStar)))

theorem infinitely_many_quantitative_counterexamples :
    ∃ ε : Nat → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ N : Nat, ∃ q, N <= q ∧ q.Prime ∧
        ∃ D : SingerDiffSet (primePowerOrder q) (q + 1),
          ∃ p : ZMod (primePowerOrder q) →
              EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))),
            Function.Injective p ∧
            (∀ {a b c d : ZMod (primePowerOrder q)},
              a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
              a ≠ b → c ≠ d →
              ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
                1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
            Metric.diam (p '' (D.carrier : Set (ZMod (primePowerOrder q)))) <=
              (cStar + ε q) * (q + 1) ^ 2 := by
  refine ⟨primePowerDiameterError, primePowerDiameterError_tendsto_zero, ?_⟩
  intro N
  obtain ⟨q, hqN, hqPrime⟩ := Nat.exists_infinite_primes N
  have hqPow : IsPrimePow q := hqPrime.isPrimePow
  obtain ⟨D, p, hinj, hsep, hdiam⟩ :=
    primePower_counterexample_exactDimension_with_diam (q := q) hqPow
  refine ⟨q, hqN, hqPrime, D, p, hinj, hsep, ?_⟩
  have hq1sq : ((q + 1 : Real) ^ 2) ≠ 0 := by positivity
  calc
    Metric.diam (p '' (D.carrier : Set _)) = primePowerDiameter q := by
      simpa [primePowerDiameter, primePowerOrder] using hdiam
    _ = (cStar + primePowerDiameterError q) * (q + 1) ^ 2 := by
      unfold primePowerDiameterError
      field_simp [hq1sq]
      ring
    _ <= (cStar + primePowerDiameterError q) * (q + 1) ^ 2 := le_rfl

/-- A compact qualitative summary of the counterexample:
there is a constant `c < 1` for which the profile function is strictly increasing and
strictly concave on `[0, pi]`, and the limiting diameter ratio equals `c`. -/
theorem erdos_counterexample_qualitative :
    ∃ c : ℝ, c < 1 ∧ c = cStar ∧
      StrictMonoOn G (Icc 0 π) ∧
      StrictConcaveOn ℝ (Icc 0 π) G ∧
      4 * H π / π ^ 2 = c := by
  exact ⟨cStar, cStar_lt_one, rfl, G_strictMonoOn, G_strictConcaveOn,
    diameter_ratio_eq_cStar⟩

/-- The concrete Euclidean realization attached to a Singer difference set:
the Fourier weights produce a map on `ZMod m` whose distances are exactly
`G (sepAngle (t - u))`, and on the Singer set those distances distinguish
unordered pairs. -/
theorem singer_realization_scaffold
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    ∃ p : ZMod m → EuclideanSpace Real (Fin (m / 2) × Fin 2),
      (∀ t u, dist (p t) (p u) = G (sepAngle (t - u))) ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier → a ≠ b →
        dist (p a) (p b) = dist (p c) (p d) →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  refine ⟨cyclicPolygonPoint (m := m) (residueClassWeight (m := m)), ?_, ?_⟩
  · intro t u
    exact cyclicResiduePoint_dist_eq_G (m := m) t u
  · intro a b c d ha hb hc hd hab hEq
    exact eq_or_eq_swap_of_cyclicResiduePoint_dist_eq (D := D) ha hb hc hd hab hEq

/-- Release-facing alias for `singer_realization_scaffold`. -/
theorem singer_realization_exists
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    ∃ p : ZMod m → EuclideanSpace Real (Fin (m / 2) × Fin 2),
      (∀ t u, dist (p t) (p u) = G (sepAngle (t - u))) ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier → a ≠ b →
        dist (p a) (p b) = dist (p c) (p d) →
          (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  simpa using singer_realization_scaffold (D := D)

/-- There are infinitely many exact finite counterexamples, indexed already by prime values of
`q`. The associated point configuration has `q + 1` points and lives in the paper's ambient
dimension `((q + 1)^2 - (q + 1)) = q^2 + q`. -/
theorem infinitely_many_exact_counterexamples :
    ∀ N : Nat, ∃ q, N <= q ∧ q.Prime ∧
      ∃ D : SingerDiffSet (q ^ 2 + q + 1) (q + 1),
        ∃ p : ZMod (q ^ 2 + q + 1) →
            EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))),
          Function.Injective p ∧
          (∀ {a b c d : ZMod (q ^ 2 + q + 1)},
            a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
            a ≠ b → c ≠ d →
            ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
              1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
          (∀ a ∈ D.carrier, ∀ b ∈ D.carrier,
            dist (p a) (p b) <=
              scaleFactor (m := q ^ 2 + q + 1) *
                gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2)) := by
  intro N
  obtain ⟨q, hqN, hqPrime⟩ := Nat.exists_infinite_primes N
  have hqPow : IsPrimePow q := hqPrime.isPrimePow
  obtain ⟨D, p, hinj, hsep, hdiam⟩ := primePower_counterexample_exactDimension (q := q) hqPow
  exact ⟨q, hqN, hqPrime, D, p, hinj, hsep, hdiam⟩

end

end DiameterConstruction
