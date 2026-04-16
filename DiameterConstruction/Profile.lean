/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import DiameterConstruction.Analysis
import DiameterConstruction.Construction
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Cyclic separation angles and the distance profile

This file packages the cyclic separation parameter attached to a difference in `ZMod m`,
and shows that on a Singer difference set the profile value `G(sepAngle (a - b))`
already distinguishes unordered pairs.
-/

namespace DiameterConstruction

open Real Set ZMod

noncomputable section

/-- The angle attached to a cyclic separation in `ZMod m`, using the closest representative. -/
def sepAngle {m : ℕ} [NeZero m] (r : ZMod m) : ℝ :=
  2 * π * (r.valMinAbs.natAbs : ℝ) / m

lemma sepAngle_nonneg {m : ℕ} [NeZero m] (r : ZMod m) : 0 ≤ sepAngle r := by
  unfold sepAngle
  positivity

lemma sepAngle_le_pi {m : ℕ} [NeZero m] (r : ZMod m) : sepAngle r ≤ π := by
  have hcastNat : (r.valMinAbs.natAbs : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
    exact_mod_cast r.natAbs_valMinAbs_le
  have htwice : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ m := by
    exact_mod_cast (Nat.mul_div_le m 2)
  have hcast : (r.valMinAbs.natAbs : ℝ) ≤ (m : ℝ) / 2 := by
    nlinarith
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero <| NeZero.ne m)
  calc
    sepAngle r = (2 * π / m) * (r.valMinAbs.natAbs : ℝ) := by
      unfold sepAngle
      ring
    _ ≤ (2 * π / m) * (m / 2) := by
      gcongr
    _ = π := by
      field_simp [hmpos.ne']

lemma sepAngle_mem_Icc {m : ℕ} [NeZero m] (r : ZMod m) : sepAngle r ∈ Set.Icc 0 π :=
  ⟨sepAngle_nonneg r, sepAngle_le_pi r⟩

lemma sepAngle_pos {m : ℕ} [NeZero m] {r : ZMod m} (hr : r ≠ 0) : 0 < sepAngle r := by
  have hvm : r.valMinAbs ≠ 0 := fun h0 => hr ((ZMod.valMinAbs_eq_zero r).mp h0)
  have hnat : 0 < r.valMinAbs.natAbs := by
    exact Int.natAbs_pos.mpr hvm
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero <| NeZero.ne m)
  have hcoeff : 0 < 2 * π / (m : ℝ) := by
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) hmpos
  calc
    0 < (2 * π / (m : ℝ)) * (r.valMinAbs.natAbs : ℝ) := by
      exact mul_pos hcoeff (by exact_mod_cast hnat)
    _ = sepAngle r := by
      unfold sepAngle
      ring

lemma sepAngle_eq_zero_iff {m : ℕ} [NeZero m] {r : ZMod m} : sepAngle r = 0 ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    exact (ne_of_gt (sepAngle_pos hr)) h
  · rintro rfl
    unfold sepAngle
    simp

lemma natAbs_eq_of_sepAngle_eq {m : ℕ} [NeZero m] {r s : ZMod m}
    (h : sepAngle r = sepAngle s) :
    r.valMinAbs.natAbs = s.valMinAbs.natAbs := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero <| NeZero.ne m).ne'
  have hpi0 : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  unfold sepAngle at h
  field_simp [hm0, hpi0] at h
  exact_mod_cast h

/-- The abstract profile distance attached to a difference in `ZMod m`. -/
def cyclicProfileDist {m : ℕ} [NeZero m] (a b : ZMod m) : ℝ :=
  G (sepAngle (a - b))

lemma cyclicProfileDist_pos
    {m : ℕ} [NeZero m] {a b : ZMod m} (hab : a ≠ b) :
    0 < cyclicProfileDist a b := by
  unfold cyclicProfileDist
  exact G_pos (sepAngle_pos (sub_ne_zero_of_ne hab)) (sepAngle_le_pi _)

/-- On a Singer difference set, equal profile values force the corresponding unordered pairs
to agree. This is the formal version of the paper's cyclic-separation indexing lemma combined
with strict monotonicity of `G`. -/
lemma eq_or_eq_swap_of_cyclicProfileDist_eq
    {m n : ℕ} [NeZero m] (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hEq : cyclicProfileDist a b = cyclicProfileDist c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hmem₁ : sepAngle (a - b) ∈ Set.Icc 0 π := sepAngle_mem_Icc (a - b)
  have hmem₂ : sepAngle (c - d) ∈ Set.Icc 0 π := sepAngle_mem_Icc (c - d)
  have hsepEq : sepAngle (a - b) = sepAngle (c - d) := by
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have hltG : G (sepAngle (a - b)) < G (sepAngle (c - d)) := G_strictMonoOn hmem₁ hmem₂ hlt
      exact (ne_of_lt hltG) (by simpa [cyclicProfileDist] using hEq)
    · have hltG : G (sepAngle (c - d)) < G (sepAngle (a - b)) := G_strictMonoOn hmem₂ hmem₁ hgt
      exact (ne_of_lt hltG) (by simpa [cyclicProfileDist] using hEq.symm)
  have hnatEq : (a - b).valMinAbs.natAbs = (c - d).valMinAbs.natAbs :=
    natAbs_eq_of_sepAngle_eq hsepEq
  exact eq_or_eq_swap_of_natAbs_sub_eq (D := D) ha hb hc hd hab hnatEq

end

end DiameterConstruction

