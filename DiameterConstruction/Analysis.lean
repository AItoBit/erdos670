/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
module

public import DiameterConstruction.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Analytic properties of H and G

This file proves the key analytic properties of the squared distance profile `H` and the
distance profile `G = √H`:

* `H` is strictly increasing on `[0, π]` with `H(0) = 0` and `H(π) = (π² - 1)/4`.
* `G` is strictly increasing on `[0, π]` (Lemma 3.2 of the paper).
* `G` is strictly concave on `[0, π]` (Lemma 3.2 of the paper).

The strict concavity is the main analytic result. The proof follows the paper:
the numerator `2H·H'' - (H')²` of `G''` is bounded above by `-ε²(1 - cos θ)² < 0`.

## Main results

* `DiameterConstruction.H_pos` : `H(θ) > 0` for `θ ∈ (0, π]`.
* `DiameterConstruction.G_strictMonoOn` : `G` is strictly increasing on `[0, π]`.
* `DiameterConstruction.G_strictConcaveOn` : `G` is strictly concave on `[0, π]`.
-/

@[expose] public section

namespace DiameterConstruction

open Real Set

noncomputable section

/-! ### Properties of H -/

@[simp]
lemma H_zero : H 0 = 0 := by
  simp [H]

lemma H_pi : H π = (π ^ 2 - 1) / 4 := by
  unfold H; norm_num; ring;

lemma hasDerivAt_H (θ : ℝ) : HasDerivAt H (H' θ) θ := by
  convert
    (HasDerivAt.sub
      (HasDerivAt.div_const (HasDerivAt.const_mul Real.pi (hasDerivAt_id θ)) 4)
      (HasDerivAt.div_const (HasDerivAt.const_sub (1 : ℝ) (Real.hasDerivAt_cos θ)) 8))
    using 1
  unfold H'
  ring

lemma H'_pos (θ : ℝ) : 0 < H' θ := by
  exact sub_pos_of_lt ( by nlinarith [ Real.pi_gt_three, Real.sin_le_one θ ] )

lemma H_pos {θ : ℝ} (hθ₀ : 0 < θ) (_hθπ : θ ≤ π) : 0 < H θ := by
  -- Since $H$ is strictly increasing on $(0, \pi]$, we have $H(θ) > H(0) = 0$.
  have hH_pos : StrictMono H := by
    exact strictMono_of_deriv_pos fun x => by rw [ hasDerivAt_H x |> HasDerivAt.deriv ] ; exact H'_pos x;
  exact lt_of_le_of_lt ( by norm_num [ H_zero ] ) ( hH_pos hθ₀ )

lemma H_nonneg {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ π) : 0 ≤ H θ := by
  exact ( if h : θ = 0 then by rw [ h ] ; exact H_zero.symm ▸ le_rfl else H_pos ( lt_of_le_of_ne hθ₀ ( Ne.symm h ) ) hθπ |> le_of_lt )

lemma H_ne_zero {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : H θ ≠ 0 :=
  ne_of_gt (H_pos hθ₀ hθπ)

lemma continuous_H : Continuous H := by
  unfold H
  fun_prop

lemma continuousOn_H : ContinuousOn H (Icc 0 π) :=
  continuous_H.continuousOn

lemma hasDerivAt_H' (θ : ℝ) : HasDerivAt H' (H'' θ) θ := by
  convert HasDerivAt.sub ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_sin θ |> HasDerivAt.div_const <| 8 ) using 1 ; norm_num [ H'' ];
  ring

/-! ### Properties of G -/

lemma G_nonneg (θ : ℝ) : 0 ≤ G θ :=
  Real.sqrt_nonneg _

lemma G_pos {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : 0 < G θ :=
  Real.sqrt_pos_of_pos (H_pos hθ₀ hθπ)

lemma G_ne_zero {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : G θ ≠ 0 :=
  ne_of_gt (G_pos hθ₀ hθπ)

@[simp]
lemma G_zero : G 0 = 0 := by
  simp [G]

lemma G_sq {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ π) : G θ ^ 2 = H θ := by
  simp [G]
  exact Real.sq_sqrt (H_nonneg hθ₀ hθπ)

lemma hasDerivAt_G {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) :
    HasDerivAt G (G' θ) θ := by
      convert HasDerivAt.sqrt ( hasDerivAt_H θ ) _ using 1;
      exact H_ne_zero hθ₀ hθπ

lemma continuousOn_G : ContinuousOn G (Icc 0 π) := by
  exact ContinuousOn.sqrt ( continuousOn_H )

/-! ### G is strictly increasing -/

lemma G_strictMonoOn : StrictMonoOn G (Icc 0 π) := by
  intros x hx y hy hxy;
  -- Since H is strictly increasing on ℝ, we have H(x) < H(y).
  have hH : DiameterConstruction.H x < DiameterConstruction.H y := by
    exact strictMono_of_deriv_pos ( fun θ => by rw [ hasDerivAt_H θ |> HasDerivAt.deriv ] ; exact H'_pos θ ) hxy;
  exact Real.sqrt_lt_sqrt ( DiameterConstruction.H_nonneg hx.1 hx.2 ) hH

/-! ### The numerator bound — key to concavity -/

/-- The auxiliary function `φ(θ) = sin θ - θ cos θ`. -/
def phi (θ : ℝ) : ℝ := sin θ - θ * cos θ

lemma phi_pos {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) : 0 < phi θ := by
  refine' sub_pos_of_lt _;
  by_cases h₂ : θ < Real.pi / 2;
  · have := Real.lt_tan hθ₀ h₂;
    rwa [ Real.tan_eq_sin_div_cos, lt_div_iff₀ ( Real.cos_pos_of_mem_Ioo ⟨ by linarith, h₂ ⟩ ) ] at this;
  · exact lt_of_le_of_lt ( mul_nonpos_of_nonneg_of_nonpos hθ₀.le ( Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith ) ( by linarith ) ) ) ( Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ )

lemma phi_lt_pi {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) : phi θ < π := by
  unfold phi;
  by_cases h₂ : θ ≤ Real.pi / 2;
  · nlinarith [ Real.sin_le_one θ, Real.cos_nonneg_of_mem_Icc ⟨ by linarith, h₂ ⟩, Real.pi_gt_three ];
  · -- Since $\theta > \frac{\pi}{2}$, we have $\cos \theta < 0$.
    have h_cos_neg : Real.cos θ < 0 := by
      exact Real.cos_neg_of_pi_div_two_lt_of_lt ( by linarith ) ( by linarith );
    have := Real.sin_lt ( show 0 < Real.pi - θ by linarith );
    norm_num at this; nlinarith [ Real.pi_le_four, Real.sin_sq_add_cos_sq θ, Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ ] ;

/-
The numerator `2H(θ)H''(θ) - H'(θ)²` equals
`-(π/4)² + 2·(π/4)·(1/8)·φ(θ) - (1/8)²·(1 - cos θ)²`.
-/
lemma G''_num_eq (θ : ℝ) :
    G''_num θ = -(π / 4) ^ 2 + 2 * (π / 4) * (1 / 8) * phi θ
      - (1 / 8) ^ 2 * (1 - cos θ) ^ 2 := by
        unfold G''_num H H' H'' phi
        ring_nf
        rw [Real.sin_sq]
        ring_nf

/-
**Key bound**: The numerator `2H·H'' - (H')²` satisfies
`2H(θ)H''(θ) - H'(θ)² ≤ -(1/64)(1 - cos θ)²`.
-/
lemma G''_num_le (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < π) :
    G''_num θ ≤ -(1 / 64) * (1 - cos θ) ^ 2 := by
      have := phi_lt_pi hθ₀ hθπ;
      rw [ G''_num_eq ] ; nlinarith [ pi_gt_three, mul_lt_mul_of_pos_left this <| Real.pi_pos ] ;

lemma G''_num_neg {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) : G''_num θ < 0 := by
  exact lt_of_le_of_lt ( G''_num_le θ hθ₀ hθπ ) ( mul_neg_of_neg_of_pos ( by norm_num ) ( sq_pos_of_pos ( sub_pos_of_lt ( by nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ ] ) ) ) )

/-! ### G is strictly concave -/

/-
The derivative of `G'` (i.e., `G''`) is `G''_num(θ) / (4 · H(θ)^(3/2))`.
-/
lemma hasDerivAt_G' {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) :
    HasDerivAt G' (G''_num θ / (4 * H θ * sqrt (H θ))) θ := by
      convert HasDerivAt.div ( hasDerivAt_H' θ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) <| HasDerivAt.sqrt ( hasDerivAt_H θ ) _ ) _ using 1;
      · norm_num [ G''_num, H'' ];
        grind;
      · exact H_ne_zero hθ₀ hθπ.le;
      · exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.sqrt_pos.mpr <| H_pos hθ₀ hθπ.le

lemma deriv_G_eq {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) :
    deriv G θ = G' θ := by
  exact (hasDerivAt_G hθ₀ hθπ.le).deriv

lemma derivG_eventuallyEq {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    deriv G =ᶠ[nhds θ] G' := by
      filter_upwards [ Ioo_mem_nhds hθ.1 hθ.2 ] with x hx;
      convert HasDerivAt.deriv ( hasDerivAt_G hx.1 hx.2.le ) using 1

lemma iteratedDeriv_two_G_neg {θ : ℝ} (hθ : θ ∈ interior (Icc 0 π)) :
    deriv^[2] G θ < 0 := by
      -- From the hypothesis hθ, we know that θ is in the interior of [0, π], which means 0 < θ < π.
      have hθ_pos : 0 < θ ∧ θ < Real.pi := by
        rwa [ interior_Icc ] at hθ;
      -- From the hypothesis hθ, we know that θ is in the interior of [0, π], which means 0 < θ < π. Therefore, we can apply the lemma hasDerivAt_G' to get the derivative of G' at θ.
      have h_deriv_G' : HasDerivAt G' (G''_num θ / (4 * H θ * Real.sqrt (H θ))) θ := by
        exact hasDerivAt_G' hθ_pos.1 hθ_pos.2;
      convert h_deriv_G'.deriv ▸ div_neg_of_neg_of_pos ( G''_num_neg hθ_pos.1 hθ_pos.2 ) _ using 1;
      · exact Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hθ_pos.1 hθ_pos.2 ) fun x hx => deriv_G_eq hx.1 hx.2 );
      · exact mul_pos ( mul_pos zero_lt_four ( H_pos hθ_pos.1 hθ_pos.2.le ) ) ( Real.sqrt_pos.mpr ( H_pos hθ_pos.1 hθ_pos.2.le ) )

/-- **Lemma 3.2 (Concavity)**: `G` is strictly concave on `[0, π]`. -/
theorem G_strictConcaveOn : StrictConcaveOn ℝ (Icc 0 π) G := by
  exact strictConcaveOn_of_deriv2_neg (convex_Icc 0 π) continuousOn_G
    fun θ hθ => iteratedDeriv_two_G_neg hθ

/-! ### Consequence for distance gaps (Corollary 3.3) -/

/-
**Corollary 3.3**: For any arithmetic grid `2πs/m` with `s = 1, …, N`,
the forward differences of `G` are strictly decreasing. In particular,
the smallest gap is the last one `G(2πN/m) - G(2π(N-1)/m)`.
-/
theorem G_gaps_decreasing {a b c : ℝ} (ha : a ∈ Icc 0 π) (hc : c ∈ Icc 0 π)
    (hab : a < b) (hbc : b < c) (hstep : c - b = b - a) :
    G c - G b < G b - G a := by
      -- By definition of $G$, we know that $G$ is strictly concave on $[0, \pi]$.
      have hG_concave : StrictConcaveOn ℝ (Set.Icc 0 Real.pi) G :=
        G_strictConcaveOn;
      have := hG_concave.2 ha hc;
      contrapose! this;
      exact ⟨ by linarith, 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [ show ( 1 / 2 : ℝ ) • a + ( 1 / 2 : ℝ ) • c = b by norm_num; linarith ] ; norm_num; linarith ⟩

end

end DiameterConstruction
