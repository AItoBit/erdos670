/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
module

public import DiameterConstruction.DiscreteProfile
public import DiameterConstruction.Singer

/-!
# Scaling the discrete realization

This file formalizes the exact finite scaling argument:

* the distances `d_s = G(2 * pi * s / m)` form a strictly increasing sequence whose
  smallest gap is the last one,
* scaling by the reciprocal of that last gap makes all distinct realized distances at
  least `1` apart,
* for every prime power `q`, the Singer realization therefore gives an exact finite
  counterexample configuration,
* and the diameter of the scaled point set is identified exactly with the top grid
  distance, both before and after reindexing into the paper's ambient dimension.
-/

@[expose] public section

namespace DiameterConstruction

open scoped Real Topology
open Real Set ZMod

noncomputable section

/-- The `s`-th grid distance `d_s = G(2 * pi * s / m)`. -/
def gridDist {m : Nat} [NeZero m] (s : Nat) : Real :=
  G (2 * Real.pi * s / m)

/-- The forward gap `d_(s + 1) - d_s`. -/
def gridGap {m : Nat} [NeZero m] (s : Nat) : Real :=
  gridDist (m := m) (s + 1) - gridDist (m := m) s

/-- The last forward gap, i.e. the smallest one in the paper. -/
def lastGap {m : Nat} [NeZero m] : Real :=
  gridGap (m := m) (m / 2 - 1)

/-- Scaling by the reciprocal of the smallest gap normalizes all distinct realized
distances to be at least `1` apart. -/
def scaleFactor {m : Nat} [NeZero m] : Real :=
  1 / lastGap (m := m)

/-- The scaled concrete realization used in the final counterexample. -/
def scaledResiduePoint {m : Nat} [NeZero m] (t : ZMod m) :
    EuclideanSpace Real (Prod (Fin (m / 2)) (Fin 2)) :=
  scaleFactor (m := m) •
    cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t

lemma sepAngle_natCast {m : Nat} [NeZero m] {s : Nat} (hs : s <= m / 2) :
    sepAngle ((s : Nat) : ZMod m) = 2 * Real.pi * s / m := by
  unfold sepAngle
  rw [ZMod.valMinAbs_natCast_of_le_half hs]
  simp

lemma gridDist_eq_sepAngle_natCast {m : Nat} [NeZero m] {s : Nat} (hs : s <= m / 2) :
    gridDist (m := m) s = G (sepAngle ((s : Nat) : ZMod m)) := by
  rw [gridDist, sepAngle_natCast (m := m) hs]

lemma gridAngle_mem_Icc {m : Nat} [NeZero m] {s : Nat} (hs : s <= m / 2) :
    2 * Real.pi * s / m ∈ Set.Icc (0 : Real) Real.pi := by
  rw [← sepAngle_natCast (m := m) hs]
  exact sepAngle_mem_Icc ((s : Nat) : ZMod m)

lemma gridDist_nonneg {m : Nat} [NeZero m] (s : Nat) : 0 <= gridDist (m := m) s := by
  exact G_nonneg _

lemma gridAngle_strictMono {m : Nat} [NeZero m] {s t : Nat}
    (_ht : t <= m / 2) (hst : s < t) :
    2 * Real.pi * s / m < 2 * Real.pi * t / m := by
  have hcoeff : 0 < 2 * Real.pi / (m : Real) := by
    have hmpos : (0 : Real) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) hmpos
  calc
    2 * Real.pi * s / m = (2 * Real.pi / (m : Real)) * s := by ring
    _ < (2 * Real.pi / (m : Real)) * t := by
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hst) hcoeff
    _ = 2 * Real.pi * t / m := by ring

lemma gridDist_strictMono {m : Nat} [NeZero m] {s t : Nat}
    (hs : s <= m / 2) (ht : t <= m / 2) (hst : s < t) :
    gridDist (m := m) s < gridDist (m := m) t := by
  exact G_strictMonoOn (gridAngle_mem_Icc (m := m) hs) (gridAngle_mem_Icc (m := m) ht)
    (gridAngle_strictMono (m := m) ht hst)

lemma gridGap_strictDecreasing {m : Nat} [NeZero m] {s : Nat}
    (_hs1 : 1 <= s) (hs3 : s + 2 <= m / 2) :
    gridGap (m := m) (s + 1) < gridGap (m := m) s := by
  have hs0 : s <= m / 2 := by
    omega
  have hs2 : s + 1 <= m / 2 := by
    omega
  have hs4 : s + 1 + 1 <= m / 2 := by
    omega
  have hdecr :=
    G_gaps_decreasing
      (a := 2 * Real.pi * ((s : Nat) : Real) / m)
      (b := 2 * Real.pi * ((s + 1 : Nat) : Real) / m)
      (c := 2 * Real.pi * ((s + 1 + 1 : Nat) : Real) / m)
      (gridAngle_mem_Icc (m := m) hs0)
      (gridAngle_mem_Icc (m := m) hs4)
      (gridAngle_strictMono (m := m) (s := s) (t := s + 1) hs2 (by omega))
      (gridAngle_strictMono (m := m) (s := s + 1) (t := s + 1 + 1) hs4 (by omega))
      (by
        have hm0 : (m : Real) ≠ 0 := by
          exact_mod_cast (NeZero.ne m)
        field_simp [hm0]
        norm_num [Nat.cast_add])
  simpa [gridGap, gridDist, Nat.add_assoc] using hdecr

lemma lastGap_le_gridGap {m : Nat} [NeZero m] {s : Nat}
    (hs1 : 1 <= s) (hs2 : s + 1 <= m / 2) :
    lastGap (m := m) <= gridGap (m := m) s := by
  let N : Nat := m / 2
  suffices haux :
      ∀ k s : Nat, 1 <= s -> s + 1 <= N -> s + k = N - 1 ->
        lastGap (m := m) <= gridGap (m := m) s by
    have hk : s + ((N - 1) - s) = N - 1 := by
      omega
    exact haux ((N - 1) - s) s hs1 (by simpa [N] using hs2) hk
  intro k
  induction k with
  | zero =>
      intro s hs1 hs2 hk
      have hs : s = N - 1 := by
        omega
      simp [lastGap, gridGap, N, hs]
  | succ k ih =>
      intro s hs1 hs2 hk
      have hs3 : s + 2 <= N := by
        omega
      have hstep : gridGap (m := m) (s + 1) < gridGap (m := m) s := by
        simpa [N] using gridGap_strictDecreasing (m := m) hs1 hs3
      have hk' : (s + 1) + k = N - 1 := by
        omega
      have hs1' : 1 <= s + 1 := by
        omega
      have hs2' : (s + 1) + 1 <= N := by
        omega
      have ih' : lastGap (m := m) <= gridGap (m := m) (s + 1) := by
        exact ih (s + 1) hs1' hs2' hk'
      exact le_trans ih' hstep.le

lemma lastGap_le_gridDist_diff {m : Nat} [NeZero m] {s t : Nat}
    (hs1 : 1 <= s) (ht : t <= m / 2) (hst : s < t) :
    lastGap (m := m) <= gridDist (m := m) t - gridDist (m := m) s := by
  have hs2 : s + 1 <= m / 2 := by
    omega
  have hgap : lastGap (m := m) <= gridGap (m := m) s :=
    lastGap_le_gridGap (m := m) hs1 hs2
  have hnext_le : gridDist (m := m) (s + 1) <= gridDist (m := m) t := by
    by_cases hEq : s + 1 = t
    · simp [hEq]
    · have hlt : s + 1 < t := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hst) hEq
      exact le_of_lt (gridDist_strictMono (m := m) hs2 ht hlt)
  have hdiff : gridGap (m := m) s <= gridDist (m := m) t - gridDist (m := m) s := by
    unfold gridGap
    linarith
  exact le_trans hgap hdiff

lemma lastGap_pos {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 < lastGap (m := m) := by
  have hmono :
      gridDist (m := m) (m / 2 - 1) < gridDist (m := m) (m / 2) := by
    apply gridDist_strictMono (m := m)
    · omega
    · exact le_rfl
    · omega
  have hsucc : m / 2 - 1 + 1 = m / 2 := by
    omega
  have hsub : 0 < gridDist (m := m) (m / 2) - gridDist (m := m) (m / 2 - 1) := by
    exact sub_pos.mpr hmono
  simpa [lastGap, gridGap, hsucc] using hsub

lemma scaleFactor_pos {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 < scaleFactor (m := m) := by
  unfold scaleFactor
  exact one_div_pos.mpr (lastGap_pos (m := m) hN)

lemma scaleFactor_nonneg {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 <= scaleFactor (m := m) := by
  exact (scaleFactor_pos (m := m) hN).le

lemma residuePoint_dist_eq_gridDist {m : Nat} [NeZero m] (a b : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
        (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) =
      gridDist (m := m) ((a - b).valMinAbs.natAbs) := by
  unfold gridDist
  rw [cyclicResiduePoint_dist_eq_G]
  rfl

lemma scaledResiduePoint_dist_eq {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
      scaleFactor (m := m) *
        dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
  unfold scaledResiduePoint
  rw [dist_smul₀, Real.norm_of_nonneg (scaleFactor_nonneg (m := m) hN)]

lemma scaledResiduePoint_injective {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    Function.Injective (scaledResiduePoint (m := m)) := by
  intro a b hab
  by_contra hne
  have hdist0 : dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) = 0 := by
    simp [hab]
  have hdistpos :
      0 < dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) := by
    rw [scaledResiduePoint_dist_eq (m := m) hN a b]
    have hraw :
        0 <
          dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
            (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
      rw [cyclicResiduePoint_dist_eq_G]
      exact G_pos (sepAngle_pos (sub_ne_zero_of_ne hne)) (sepAngle_le_pi _)
    exact mul_pos (scaleFactor_pos (m := m) hN) hraw
  exact (ne_of_gt hdistpos) hdist0

lemma residuePoint_dist_gap_ge_lastGap
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    lastGap (m := m) <=
      |dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) -
        dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) c)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) d)| := by
  let s1 : Nat := (a - b).valMinAbs.natAbs
  let s2 : Nat := (c - d).valMinAbs.natAbs
  have hs1pos : 1 <= s1 := by
    exact Nat.succ_le_of_lt <| Int.natAbs_pos.mpr <| by
      exact (ZMod.valMinAbs_eq_zero (a - b)).not.mpr (sub_ne_zero_of_ne hab)
  have hs2pos : 1 <= s2 := by
    exact Nat.succ_le_of_lt <| Int.natAbs_pos.mpr <| by
      exact (ZMod.valMinAbs_eq_zero (c - d)).not.mpr (sub_ne_zero_of_ne hcd)
  have hs1le : s1 <= m / 2 := by
    simpa [s1] using ZMod.natAbs_valMinAbs_le (a - b)
  have hs2le : s2 <= m / 2 := by
    simpa [s2] using ZMod.natAbs_valMinAbs_le (c - d)
  have hsneq : s1 ≠ s2 := by
    intro hs
    exact hpair <|
      eq_or_eq_swap_of_natAbs_sub_eq (D := D) ha hb hc hd hab <| by
        simpa [s1, s2] using hs
  rcases lt_or_gt_of_ne hsneq with hlt | hgt
  · have hgap : lastGap (m := m) <= gridDist (m := m) s2 - gridDist (m := m) s1 :=
      lastGap_le_gridDist_diff (m := m) hs1pos hs2le hlt
    have hmono : gridDist (m := m) s1 < gridDist (m := m) s2 :=
      gridDist_strictMono (m := m) hs1le hs2le hlt
    rw [residuePoint_dist_eq_gridDist (m := m) a b, residuePoint_dist_eq_gridDist (m := m) c d]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmono.le)]
    exact hgap
  · have hgap : lastGap (m := m) <= gridDist (m := m) s1 - gridDist (m := m) s2 :=
      lastGap_le_gridDist_diff (m := m) hs2pos hs1le hgt
    have hmono : gridDist (m := m) s2 < gridDist (m := m) s1 :=
      gridDist_strictMono (m := m) hs2le hs1le hgt
    rw [residuePoint_dist_eq_gridDist (m := m) a b, residuePoint_dist_eq_gridDist (m := m) c d]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono.le)]
    exact hgap

lemma scaledResiduePoint_dist_gap_ge_one
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    1 <=
      |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
        dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| := by
  let A : Real :=
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b)
  let B : Real :=
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) c)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) d)
  have hgap :
      lastGap (m := m) <= |A - B| := by
    simpa [A, B] using
      residuePoint_dist_gap_ge_lastGap (m := m) D ha hb hc hd hab hcd hpair
  have hscale1 := scaledResiduePoint_dist_eq (m := m) hN a b
  have hscale2 := scaledResiduePoint_dist_eq (m := m) hN c d
  have hscale_nonneg : 0 <= scaleFactor (m := m) := scaleFactor_nonneg (m := m) hN
  have hlast_ne : lastGap (m := m) ≠ 0 := (lastGap_pos (m := m) hN).ne'
  have hone : 1 = scaleFactor (m := m) * lastGap (m := m) := by
    rw [scaleFactor]
    exact (one_div_mul_cancel hlast_ne).symm
  have hscaled_abs :
      |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
        dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| =
      scaleFactor (m := m) * |A - B| := by
    rw [hscale1, hscale2]
    change
      |scaleFactor (m := m) * A - scaleFactor (m := m) * B| =
        scaleFactor (m := m) * |A - B|
    calc
      |scaleFactor (m := m) * A - scaleFactor (m := m) * B|
          = |scaleFactor (m := m) * (A - B)| := by
              congr 1
              ring
      _ = |scaleFactor (m := m)| * |A - B| := by
            rw [abs_mul]
      _ = scaleFactor (m := m) * |A - B| := by
            rw [abs_of_nonneg hscale_nonneg]
  calc
    1 = scaleFactor (m := m) * lastGap (m := m) := hone
    _ <= scaleFactor (m := m) * |A - B| := by
      exact mul_le_mul_of_nonneg_left hgap hscale_nonneg
    _ =
        |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
          dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| := by
            exact hscaled_abs.symm

lemma scaledResiduePoint_dist_le_top
    {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) <=
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  rw [scaledResiduePoint_dist_eq (m := m) hN a b]
  refine mul_le_mul_of_nonneg_left ?_ (scaleFactor_nonneg (m := m) hN)
  by_cases hab : a = b
  · simp [hab, gridDist_nonneg]
  · rw [residuePoint_dist_eq_gridDist (m := m) a b]
    let s : Nat := (a - b).valMinAbs.natAbs
    have hsle : s <= m / 2 := by
      simpa [s] using ZMod.natAbs_valMinAbs_le (a - b)
    rcases eq_or_lt_of_le hsle with hsEq | hslt
    · simp [s, hsEq]
    · exact le_of_lt (gridDist_strictMono (m := m) hsle (le_rfl : m / 2 <= m / 2) hslt)

lemma topSeparation_nonzero {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    (((m / 2 : Nat) : ZMod m)) ≠ 0 := by
  intro hzero
  have hdiv : m ∣ m / 2 := (ZMod.natCast_eq_zero_iff (m / 2) m).1 hzero
  rcases hdiv with ⟨k, hk⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    have hhalf_zero : m / 2 = 0 := by simpa [hkzero] using hk
    omega
  have hkone : 1 <= k := Nat.succ_le_of_lt hkpos
  have hm_le_half : m <= m / 2 := by
    calc
      m = m * 1 := by rw [Nat.mul_one]
      _ <= m * k := Nat.mul_le_mul_left m hkone
      _ = m / 2 := hk.symm
  have hhalf_lt : m / 2 < m := Nat.div_lt_self hmpos (by omega)
  exact (Nat.not_le_of_gt hhalf_lt) hm_le_half

lemma scaledResiduePoint_exists_top_distance
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    ∃ a ∈ D.carrier, ∃ b ∈ D.carrier,
      dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
        scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  have hr0 : (((m / 2 : Nat) : ZMod m)) ≠ 0 := topSeparation_nonzero (m := m) hN
  obtain ⟨p, hp, _⟩ := D.diff_unique ((m / 2 : Nat) : ZMod m) hr0
  rcases p with ⟨a, b⟩
  rcases hp with ⟨ha, hb, hab⟩
  refine ⟨a, ha, b, hb, ?_⟩
  have hs :
      ((a - b).valMinAbs.natAbs) = m / 2 := by
    rw [hab]
    simpa using congrArg Int.natAbs
      (ZMod.valMinAbs_natCast_of_le_half (n := m) (a := m / 2)
        (le_rfl : m / 2 <= m / 2))
  calc
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
        scaleFactor (m := m) *
          dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
            (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
          exact scaledResiduePoint_dist_eq (m := m) hN a b
    _ = scaleFactor (m := m) * gridDist (m := m) ((a - b).valMinAbs.natAbs) := by
          rw [residuePoint_dist_eq_gridDist (m := m) a b]
    _ = scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
          rw [hs]

/-- The scaled Singer configuration as a subset of the concrete Euclidean space
`R^(2 * floor(m / 2))`, presented in the paired-coordinate form. -/
def scaledSingerPointSet {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Set (EuclideanSpace Real (Prod (Fin (m / 2)) (Fin 2))) :=
  scaledResiduePoint (m := m) '' (D.carrier : Set (ZMod m))

lemma scaledSingerPointSet_bounded
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Bornology.IsBounded (scaledSingerPointSet (m := m) D) := by
  apply Set.Finite.isBounded
  simpa [scaledSingerPointSet] using
    (Finset.finite_toSet D.carrier).image (scaledResiduePoint (m := m))

lemma scaledResiduePoint_diam_eq_top
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    Metric.diam (scaledSingerPointSet (m := m) D) =
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  refine le_antisymm ?_ ?_
  · refine Metric.diam_le_of_forall_dist_le
      (mul_nonneg (scaleFactor_nonneg (m := m) hN) (gridDist_nonneg (m := m) (m / 2))) ?_
    intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact scaledResiduePoint_dist_le_top (m := m) hN a b
  · obtain ⟨a, ha, b, hb, hdist⟩ := scaledResiduePoint_exists_top_distance (m := m) hN D
    have hmema : scaledResiduePoint (m := m) a ∈ scaledSingerPointSet (m := m) D := ⟨a, ha, rfl⟩
    have hmemb : scaledResiduePoint (m := m) b ∈ scaledSingerPointSet (m := m) D := ⟨b, hb, rfl⟩
    calc
      scaleFactor (m := m) * gridDist (m := m) (m / 2) =
          dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) := by
            exact hdist.symm
      _ <= Metric.diam (scaledSingerPointSet (m := m) D) := by
            exact Metric.dist_le_diam_of_mem (scaledSingerPointSet_bounded (m := m) D) hmema hmemb

/-- Exact finite counterexample theorem for every prime power `q`.

This is the full finite construction from the paper: a Singer difference set,
the concrete Euclidean realization, the scaling argument giving pairwise
distance separation at least `1`, and an explicit uniform upper bound on the
diameter. -/
theorem primePower_counterexample
    {q : Nat} (hq : IsPrimePow q) :
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq2 : 2 <= q := hq.two_le
      omega⟩
    ∃ D : SingerDiffSet m (q + 1),
      let p := scaledResiduePoint (m := m)
      Function.Injective p ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
        a ≠ b → c ≠ d →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
      (∀ a ∈ D.carrier, ∀ b ∈ D.carrier,
        dist (p a) (p b) <= scaleFactor (m := m) * gridDist (m := m) (m / 2)) := by
  classical
  dsimp
  have hq2 : 2 <= q := hq.two_le
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq2 hq2
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  have hN : 2 <= (q ^ 2 + q + 1) / 2 := by
    exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)
  obtain ⟨D⟩ := singer_exists hq
  refine ⟨D, scaledResiduePoint_injective (m := q ^ 2 + q + 1) hN, ?_, ?_⟩
  · intro a b c d ha hb hc hd hab hcd hpair
    exact
      scaledResiduePoint_dist_gap_ge_one
        (m := q ^ 2 + q + 1) hN D ha hb hc hd hab hcd hpair
  · intro a ha b hb
    exact scaledResiduePoint_dist_le_top (m := q ^ 2 + q + 1) hN a b

/-- The scaled realization reindexed as a point in `R^(2 * floor(m / 2))`. -/
def scaledResiduePointFin {m : Nat} [NeZero m] (t : ZMod m) :
    EuclideanSpace Real (Fin ((m / 2) * 2)) :=
  polygonPointReindex (scaledResiduePoint (m := m) t)

lemma scaledResiduePointFin_dist_eq {m : Nat} [NeZero m] (a b : ZMod m) :
    dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) =
      dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) := by
  rw [scaledResiduePointFin]
  exact (polygonPointReindex (N := m / 2)).dist_map
    (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b)

lemma scaledResiduePointFin_injective {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    Function.Injective (scaledResiduePointFin (m := m)) := by
  exact (polygonPointReindex (N := m / 2)).injective.comp
    (scaledResiduePoint_injective (m := m) hN)

lemma scaledResiduePointFin_dist_gap_ge_one
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    1 <=
      |dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) -
        dist (scaledResiduePointFin (m := m) c) (scaledResiduePointFin (m := m) d)| := by
  simpa [scaledResiduePointFin_dist_eq (m := m) a b, scaledResiduePointFin_dist_eq (m := m) c d]
    using scaledResiduePoint_dist_gap_ge_one (m := m) hN D ha hb hc hd hab hcd hpair

lemma scaledResiduePointFin_dist_le_top
    {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) <=
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  simpa [scaledResiduePointFin_dist_eq (m := m) a b] using
    scaledResiduePoint_dist_le_top (m := m) hN a b

/-- The scaled Singer configuration in the reindexed Euclidean space `R^(2 * floor(m / 2))`. -/
def scaledSingerPointSetFin {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Set (EuclideanSpace Real (Fin ((m / 2) * 2))) :=
  scaledResiduePointFin (m := m) '' (D.carrier : Set (ZMod m))

lemma scaledSingerPointSetFin_bounded
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Bornology.IsBounded (scaledSingerPointSetFin (m := m) D) := by
  apply Set.Finite.isBounded
  simpa [scaledSingerPointSetFin] using
    (Finset.finite_toSet D.carrier).image (scaledResiduePointFin (m := m))

lemma scaledResiduePointFin_exists_top_distance
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    ∃ a ∈ D.carrier, ∃ b ∈ D.carrier,
      dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) =
        scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  obtain ⟨a, ha, b, hb, hdist⟩ := scaledResiduePoint_exists_top_distance (m := m) hN D
  refine ⟨a, ha, b, hb, ?_⟩
  simpa [scaledResiduePointFin_dist_eq (m := m) a b] using hdist

lemma scaledResiduePointFin_diam_eq_top
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    Metric.diam (scaledSingerPointSetFin (m := m) D) =
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  refine le_antisymm ?_ ?_
  · refine Metric.diam_le_of_forall_dist_le
      (mul_nonneg (scaleFactor_nonneg (m := m) hN) (gridDist_nonneg (m := m) (m / 2))) ?_
    intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact scaledResiduePointFin_dist_le_top (m := m) hN a b
  · obtain ⟨a, ha, b, hb, hdist⟩ := scaledResiduePointFin_exists_top_distance (m := m) hN D
    have hmema : scaledResiduePointFin (m := m) a ∈ scaledSingerPointSetFin (m := m) D :=
      ⟨a, ha, rfl⟩
    have hmemb : scaledResiduePointFin (m := m) b ∈ scaledSingerPointSetFin (m := m) D :=
      ⟨b, hb, rfl⟩
    calc
      scaleFactor (m := m) * gridDist (m := m) (m / 2) =
          dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) := by
            exact hdist.symm
      _ <= Metric.diam (scaledSingerPointSetFin (m := m) D) := by
            exact Metric.dist_le_diam_of_mem (scaledSingerPointSetFin_bounded (m := m) D)
              hmema hmemb

/-- Exact finite counterexample theorem, now reindexed into `R^(2 * floor(m / 2))`. -/
theorem primePower_counterexample_fin
    {q : Nat} (hq : IsPrimePow q) :
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq2 : 2 <= q := hq.two_le
      omega⟩
    ∃ D : SingerDiffSet m (q + 1),
      let p := scaledResiduePointFin (m := m)
      Function.Injective p ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
        a ≠ b → c ≠ d →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
      (∀ a ∈ D.carrier, ∀ b ∈ D.carrier,
        dist (p a) (p b) <= scaleFactor (m := m) * gridDist (m := m) (m / 2)) := by
  classical
  dsimp
  have hq2 : 2 <= q := hq.two_le
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq2 hq2
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  have hN : 2 <= (q ^ 2 + q + 1) / 2 := by
    exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)
  obtain ⟨D⟩ := singer_exists hq
  refine ⟨D, scaledResiduePointFin_injective (m := q ^ 2 + q + 1) hN, ?_, ?_⟩
  · intro a b c d ha hb hc hd hab hcd hpair
    exact
      scaledResiduePointFin_dist_gap_ge_one
        (m := q ^ 2 + q + 1) hN D ha hb hc hd hab hcd hpair
  · intro a ha b hb
    exact scaledResiduePointFin_dist_le_top (m := q ^ 2 + q + 1) hN a b

/-- The reindexed finite counterexample comes with an exact diameter formula:
the top cyclic separation is attained, so the diameter is exactly the scaled top grid distance. -/
theorem primePower_counterexample_fin_with_diam
    {q : Nat} (hq : IsPrimePow q) :
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq2 : 2 <= q := hq.two_le
      omega⟩
    ∃ D : SingerDiffSet m (q + 1),
      let p := scaledResiduePointFin (m := m)
      Function.Injective p ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
        a ≠ b → c ≠ d →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
      Metric.diam (scaledSingerPointSetFin (m := m) D) =
        scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  classical
  dsimp
  have hq2 : 2 <= q := hq.two_le
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq2 hq2
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  have hN : 2 <= (q ^ 2 + q + 1) / 2 := by
    exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)
  obtain ⟨D⟩ := singer_exists hq
  refine ⟨D, scaledResiduePointFin_injective (m := q ^ 2 + q + 1) hN, ?_,
    scaledResiduePointFin_diam_eq_top (m := q ^ 2 + q + 1) hN D⟩
  intro a b c d ha hb hc hd hab hcd hpair
  exact
    scaledResiduePointFin_dist_gap_ge_one
      (m := q ^ 2 + q + 1) hN D ha hb hc hd hab hcd hpair

lemma primePower_reindexed_dim (q : Nat) :
    ((q ^ 2 + q + 1) / 2) * 2 = q ^ 2 + q := by
  have hfactor : q ^ 2 + q = q * (q + 1) := by
    calc
      q ^ 2 + q = q * q + q * 1 := by rw [pow_two, Nat.mul_one]
      _ = q * (q + 1) := by rw [Nat.mul_add]
  have hEven : 2 ∣ q ^ 2 + q := by
    by_cases hqEven : 2 ∣ q
    · rw [hfactor]
      exact dvd_mul_of_dvd_left hqEven (q + 1)
    · have hq1 : 2 ∣ q + 1 := by
        rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
        · exact False.elim <| hqEven (Nat.dvd_of_mod_eq_zero h0)
        · exact Nat.dvd_of_mod_eq_zero (by omega)
      rw [hfactor]
      exact dvd_mul_of_dvd_right hq1 q
  rcases hEven with ⟨k, hk⟩
  rw [hk]
  omega

lemma primePower_ambientDim_eq_n (q : Nat) :
    ((q ^ 2 + q + 1) / 2) * 2 = (q + 1) ^ 2 - (q + 1) := by
  calc
    ((q ^ 2 + q + 1) / 2) * 2 = q ^ 2 + q := primePower_reindexed_dim q
    _ = (q + 1) ^ 2 - (q + 1) := by
      calc
        q ^ 2 + q = (q + 1) * q := by
          rw [Nat.succ_mul, pow_two]
        _ = (q + 1) ^ 2 - (q + 1) := by
          rw [pow_two, Nat.mul_succ, Nat.add_sub_cancel]

/-- Exact finite counterexample theorem in the paper's ambient dimension `R^(n^2 - n)`. -/
theorem primePower_counterexample_exactDimension
    {q : Nat} (hq : IsPrimePow q) :
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
            scaleFactor (m := q ^ 2 + q + 1) * gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2)) := by
  classical
  have hdim : ((q ^ 2 + q + 1) / 2) * 2 = (q + 1) ^ 2 - (q + 1) :=
    primePower_ambientDim_eq_n q
  let e :
      EuclideanSpace Real (Fin (((q ^ 2 + q + 1) / 2) * 2)) ≃ₗᵢ[Real]
        EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))) :=
    LinearIsometryEquiv.piLpCongrLeft 2 Real Real (finCongr hdim)
  obtain ⟨D, hinj, hsep, hdiam⟩ := primePower_counterexample_fin (q := q) hq
  refine ⟨D, fun t => e (scaledResiduePointFin (m := q ^ 2 + q + 1) t), ?_, ?_, ?_⟩
  · exact e.injective.comp hinj
  · intro a b c d ha hb hc hd hab hcd hpair
    simpa [e.dist_map] using hsep ha hb hc hd hab hcd hpair
  · intro a ha b hb
    simpa [e.dist_map] using hdiam a ha b hb

/-- Exact finite counterexample theorem in the paper's ambient dimension `R^(n^2 - n)`,
with the exact diameter formula included. -/
theorem primePower_counterexample_exactDimension_with_diam
    {q : Nat} (hq : IsPrimePow q) :
    ∃ D : SingerDiffSet (q ^ 2 + q + 1) (q + 1),
      ∃ p : ZMod (q ^ 2 + q + 1) →
          EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))),
        Function.Injective p ∧
        (∀ {a b c d : ZMod (q ^ 2 + q + 1)},
          a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
          a ≠ b → c ≠ d →
          ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
            1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
        Metric.diam (p '' (D.carrier : Set (ZMod (q ^ 2 + q + 1)))) =
          scaleFactor (m := q ^ 2 + q + 1) * gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2) := by
  classical
  have hdim : ((q ^ 2 + q + 1) / 2) * 2 = (q + 1) ^ 2 - (q + 1) :=
    primePower_ambientDim_eq_n q
  let e :
      EuclideanSpace Real (Fin (((q ^ 2 + q + 1) / 2) * 2)) ≃ₗᵢ[Real]
        EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))) :=
    LinearIsometryEquiv.piLpCongrLeft 2 Real Real (finCongr hdim)
  obtain ⟨D, hinj, hsep, _hdiamUpper⟩ := primePower_counterexample_fin (q := q) hq
  have hdiam : Metric.diam (scaledSingerPointSetFin (m := q ^ 2 + q + 1) D) =
      scaleFactor (m := q ^ 2 + q + 1) * gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2) :=
    scaledResiduePointFin_diam_eq_top (m := q ^ 2 + q + 1) (by
      have hq2 : 2 <= q := hq.two_le
      have hqq : 4 <= q * q := by
        simpa using Nat.mul_le_mul hq2 hq2
      have hm4 : 4 <= q ^ 2 + q + 1 := by
        rw [pow_two]
        omega
      exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)) D
  refine ⟨D, fun t => e (scaledResiduePointFin (m := q ^ 2 + q + 1) t), ?_, ?_, ?_⟩
  · exact e.injective.comp hinj
  · intro a b c d ha hb hc hd hab hcd hpair
    simpa [e.dist_map] using hsep ha hb hc hd hab hcd hpair
  · simpa [scaledSingerPointSetFin, image_image] using
      (e.diam_image (scaledSingerPointSetFin (m := q ^ 2 + q + 1) D)).trans hdiam

end

end DiameterConstruction

