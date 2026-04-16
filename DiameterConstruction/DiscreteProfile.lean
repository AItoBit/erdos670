/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import DiameterConstruction.Fourier
import DiameterConstruction.Realization

/-!
# The discrete profile realized by the Fourier weights

This file packages the paper's specific finite weight family

`W_r = sum_{j odd, j congruent to plus or minus r mod m} c_j`

coming from the perturbed odd Fourier coefficients. It proves that the resulting
weighted polygon profile agrees with `H` on the cyclic grid `sepAngle : ZMod m -> R`,
so the realized Euclidean distances are exactly `G(sepAngle (t - u))`.
-/

namespace DiameterConstruction

open scoped Real Topology
open Real Set ZMod

noncomputable section

/-- The least absolute residue of a natural frequency modulo `m`. -/
def residueNatAbs {m : Nat} [NeZero m] (j : Nat) : Nat :=
  ((j : ZMod m).valMinAbs.natAbs)

/-- The least absolute residue of the odd frequency `2k + 1` modulo `m`. -/
def oddResidueNatAbs {m : Nat} [NeZero m] (k : Nat) : Nat :=
  residueNatAbs (m := m) (2 * k + 1)

lemma residueNatAbs_le_half {m : Nat} [NeZero m] (j : Nat) :
    residueNatAbs (m := m) j <= m / 2 := by
  simpa [residueNatAbs] using (ZMod.natAbs_valMinAbs_le (j : ZMod m))

lemma oddResidueNatAbs_le_half {m : Nat} [NeZero m] (k : Nat) :
    oddResidueNatAbs (m := m) k <= m / 2 := by
  simpa [oddResidueNatAbs] using residueNatAbs_le_half (m := m) (2 * k + 1)

lemma hasSum_two_mul_perturbedOddCoeff :
    HasSum (fun k : Nat => (2 : Real) * perturbedOddCoeff k) (H Real.pi) := by
  have hpi : HasSum (fun k : Nat =>
      perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi))) (H Real.pi) := by
    simpa using hasSum_perturbedOddCoeff_profile (θ := Real.pi)
      (show Real.pi ∈ Set.Icc (0 : Real) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩)
  refine hpi.congr_fun ?_
  intro k
  have hcos : Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi) = -1 := by
    rw [Real.cos_nat_mul_pi]
    norm_num
  calc
    (2 : Real) * perturbedOddCoeff k
      = perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi)) := by
          rw [hcos]
          ring

/-- The perturbed odd coefficients form a summable series. -/
lemma hasSum_perturbedOddCoeff :
    HasSum perturbedOddCoeff (H Real.pi / 2) := by
  have hscaled := hasSum_two_mul_perturbedOddCoeff.mul_left ((1 : Real) / 2)
  convert hscaled using 1 with k
  · ring_nf
  · ring_nf

lemma summable_perturbedOddCoeff : Summable perturbedOddCoeff :=
  hasSum_perturbedOddCoeff.summable

/-- The real weight assigned to the residue class `+-r (mod m)`. -/
def residueClassWeightReal {m : Nat} [NeZero m] (r : Fin (m / 2)) : Real :=
  ∑' k : Nat,
    if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0

/-- The corresponding nonnegative weight used in the Euclidean realization. -/
def residueClassWeight {m : Nat} [NeZero m] (r : Fin (m / 2)) : NNReal :=
  Real.toNNReal (residueClassWeightReal (m := m) r)

lemma summable_residueClassWeightReal_summand {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    Summable (fun k : Nat =>
      if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) := by
  have hnonneg : ∀ k : Nat,
      0 <= if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0 := by
    intro k
    by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
    · simp [hk, (perturbedOddCoeff_pos k).le]
    · simp [hk]
  have hle : ∀ k : Nat,
      (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0)
        <= perturbedOddCoeff k := by
    intro k
    by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
    · simp [hk]
    · simp [hk, (perturbedOddCoeff_pos k).le]
  exact Summable.of_nonneg_of_le hnonneg hle summable_perturbedOddCoeff

lemma residueClassWeightReal_nonneg {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    0 <= residueClassWeightReal (m := m) r := by
  unfold residueClassWeightReal
  refine tsum_nonneg ?_
  intro k
  by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
  · simp [hk, (perturbedOddCoeff_pos k).le]
  · simp [hk]

@[simp] lemma coe_residueClassWeight {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    ((residueClassWeight (m := m) r : NNReal) : Real) = residueClassWeightReal (m := m) r := by
  simp [residueClassWeight, Real.toNNReal_of_nonneg, residueClassWeightReal_nonneg]

/-- The raw angular parameter `2*pi*t/m` attached to `t in ZMod m`. -/
def cyclicRawAngle {m : Nat} [NeZero m] (t : ZMod m) : Real :=
  2 * Real.pi * (t.val : Real) / m

lemma cos_mul_raw_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (x : ZMod m) :
    Real.cos ((f : Real) * cyclicRawAngle (m := m) x) =
      Real.cos ((f : Real) * sepAngle x) := by
  simpa [cyclicRawAngle] using
    (cos_mul_raw_sub_eq_cos_mul_sepAngle (m := m) (f := f) x 0)

lemma cos_nat_mul_raw_eq_cos_residueNatAbs_mul_raw {m : Nat} [NeZero m]
    (j : Nat) (x : ZMod m) :
    Real.cos ((j : Real) * cyclicRawAngle (m := m) x) =
      Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
  let z : Int := ((j : ZMod m).valMinAbs)
  have hz : ((z : Int) : ZMod m) = (j : ZMod m) := by
    simp [z]
  have hzero : (((j : Int) - z : Int) : ZMod m) = 0 := by
    simp [Int.cast_sub, hz, z]
  have hdiv : (m : Int) ∣ ((j : Int) - z) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rcases hdiv with ⟨k, hk⟩
  have hkInt : (j : Int) = z + k * m := by
    linarith
  have hkReal : (j : Real) = (z : Real) + k * m := by
    exact_mod_cast hkInt
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m)).ne'
  have hperiod :
      (j : Real) * cyclicRawAngle (m := m) x =
        (z : Real) * cyclicRawAngle (m := m) x +
          (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi) := by
    calc
      (j : Real) * cyclicRawAngle (m := m) x
          = ((z : Real) + k * m) * cyclicRawAngle (m := m) x := by
              rw [hkReal]
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (k : Real) * (m : Real) * cyclicRawAngle (m := m) x := by
            ring
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (k : Real) * ((x.val : Real) * (2 * Real.pi)) := by
            unfold cyclicRawAngle
            field_simp [hm0]
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi) := by
            have hcast : (((k * (x.val : Int)) : Int) : Real) = (k : Real) * (x.val : Real) := by
              exact_mod_cast (show (k * (x.val : Int) : Int) = k * (x.val : Int) by rfl)
            rw [hcast]
            ring
  calc
    Real.cos ((j : Real) * cyclicRawAngle (m := m) x)
        = Real.cos ((z : Real) * cyclicRawAngle (m := m) x +
            (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi)) := by
            rw [hperiod]
    _ = Real.cos ((z : Real) * cyclicRawAngle (m := m) x) := by
      rw [Real.cos_add_int_mul_two_pi]
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
      by_cases hz' : 0 <= z
      · have hcast : ((residueNatAbs (m := m) j : Nat) : Real) = (z : Real) := by
          simpa [residueNatAbs, z] using
            (show ((z.natAbs : Nat) : Real) = (z : Real) by
              rw [← Int.cast_natCast, Int.natAbs_of_nonneg hz'])
        rw [hcast]
      · have hz'' : z <= 0 := le_of_not_ge hz'
        have hcast : ((residueNatAbs (m := m) j : Nat) : Real) = -(z : Real) := by
          simpa [residueNatAbs, z] using
            (show ((z.natAbs : Nat) : Real) = -(z : Real) by
              rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hz'', Int.cast_neg])
        rw [hcast]
        have hneg :
            (-(z : Real)) * cyclicRawAngle (m := m) x =
              -((z : Real) * cyclicRawAngle (m := m) x) := by
          ring
        rw [hneg, Real.cos_neg]

lemma cos_nat_mul_sepAngle_eq_cos_residueNatAbs_mul_sepAngle {m : Nat} [NeZero m]
    (j : Nat) (x : ZMod m) :
    Real.cos ((j : Real) * sepAngle x) =
      Real.cos ((residueNatAbs (m := m) j : Real) * sepAngle x) := by
  calc
    Real.cos ((j : Real) * sepAngle x)
        = Real.cos ((j : Real) * cyclicRawAngle (m := m) x) := by
            symm
            exact cos_mul_raw_eq_cos_mul_sepAngle (m := m) j x
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
          exact cos_nat_mul_raw_eq_cos_residueNatAbs_mul_raw (m := m) j x
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * sepAngle x) := by
          exact cos_mul_raw_eq_cos_mul_sepAngle (m := m) (residueNatAbs (m := m) j) x

lemma polygonFrequency_pos {N : Nat} (r : Fin N) : 0 < polygonFrequency r := by
  simp [polygonFrequency]

lemma polygonFrequency_injective {N : Nat} :
    Function.Injective (@polygonFrequency N) := by
  intro r s h
  apply Fin.ext
  have h' : Nat.succ r.1 = Nat.succ s.1 := by
    simpa [polygonFrequency, Nat.succ_eq_add_one] using h
  exact Nat.succ.inj h'

lemma sum_if_eq_polygonFrequency {m : Nat} (n : Nat) (hn : n <= m / 2) (a : Real) :
    ∑ r : Fin (m / 2), (if n = polygonFrequency r then a else 0) =
      if n = 0 then 0 else a := by
  classical
  by_cases hn0 : n = 0
  · simp [hn0, polygonFrequency]
  · let r0 : Fin (m / 2) := ⟨n - 1, by omega⟩
    have hr0 : polygonFrequency r0 = n := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      dsimp [polygonFrequency, r0]
      omega
    rw [Finset.sum_eq_single r0]
    · simp [hr0, hn0]
    · intro r _ hrne
      by_cases hEq : n = polygonFrequency r
      · exfalso
        apply hrne
        exact polygonFrequency_injective (by simpa [hr0] using hEq.symm)
      · simp [hEq]
    · intro hr0mem
      simp at hr0mem

lemma sum_residueClassContribution {m : Nat} [NeZero m] (x : ZMod m) (k : Nat) :
    ∑ r : Fin (m / 2),
      (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
        (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x)) =
      perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
  let residue := oddResidueNatAbs (m := m) k
  let target :=
    perturbedOddCoeff k * (1 - Real.cos ((residue : Real) * sepAngle x))
  have hsum :
      ∑ r : Fin (m / 2),
        (if residue = polygonFrequency r then perturbedOddCoeff k else 0) *
          (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x)) =
        if residue = 0 then 0 else target := by
    calc
      ∑ r : Fin (m / 2),
          (if residue = polygonFrequency r then perturbedOddCoeff k else 0) *
            (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
          =
            ∑ r : Fin (m / 2),
              if residue = polygonFrequency r then target else 0 := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                by_cases hmatch : residue = polygonFrequency r
                · simp [hmatch, target]
                · simp [hmatch]
      _ = if residue = 0 then 0 else target := by
            exact sum_if_eq_polygonFrequency (n := residue)
              (hn := oddResidueNatAbs_le_half (m := m) k) target
  have htarget :
      target =
        perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
    unfold target residue oddResidueNatAbs
    congr 2
    symm
    exact cos_nat_mul_sepAngle_eq_cos_residueNatAbs_mul_sepAngle (m := m) (2 * k + 1) x
  calc
    ∑ r : Fin (m / 2),
        (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
          (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
      = if oddResidueNatAbs (m := m) k = 0 then 0 else target := by
          simpa [residue] using hsum
    _ = target := by
          by_cases hzero : oddResidueNatAbs (m := m) k = 0
          · simp [residue, target, hzero]
          · simp [hzero]
    _ = perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
          exact htarget

/-- The polygon profile coming from the grouped Fourier weights agrees with the
perturbed odd Fourier series on the cyclic grid. -/
theorem polygonSqProfile_residueClassWeight_eq_tsum {m : Nat} [NeZero m] (x : ZMod m) :
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x) =
      ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
  let g : Fin (m / 2) -> Nat -> Real := fun r k =>
    (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
      (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
  have hs :
      ∀ r ∈ (Finset.univ : Finset (Fin (m / 2))), Summable (g r) := by
    intro r hr
    unfold g
    exact (summable_residueClassWeightReal_summand (m := m) r).mul_right
      (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
  calc
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x)
        = ∑ r : Fin (m / 2), ∑' k : Nat, g r k := by
            unfold polygonSqProfile
            refine Finset.sum_congr rfl ?_
            intro r hr
            unfold g
            simpa [residueClassWeightReal] using
              ((summable_residueClassWeightReal_summand (m := m) r).tsum_mul_right
                (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))).symm
    _ = ∑' k : Nat, ∑ r : Fin (m / 2), g r k := by
          symm
          exact Summable.tsum_finsetSum hs
    _ = ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
          refine tsum_congr ?_
          intro k
          simpa [g] using sum_residueClassContribution (m := m) x k

/-- On the cyclic grid, the weighted polygon profile is exactly the explicit profile `H`. -/
theorem polygonSqProfile_residueClassWeight_eq_H {m : Nat} [NeZero m] (x : ZMod m) :
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x) = H (sepAngle x) := by
  have htheta : sepAngle x ∈ Set.Icc 0 Real.pi := sepAngle_mem_Icc x
  calc
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x)
      = ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) :=
          polygonSqProfile_residueClassWeight_eq_tsum (m := m) x
    _ = H (sepAngle x) := by
          simpa using (H_eq_tsum_perturbedOddCoeff htheta).symm

/-- The concrete cyclic Euclidean realization attached to the Fourier weights has
squared distances given exactly by `H`. -/
theorem cyclicResiduePoint_dist_sq_eq_H {m : Nat} [NeZero m] (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) ^ 2 =
        H (sepAngle (t - u)) := by
  rw [cyclicPolygonPoint_dist_sq_eq_profile (m := m) (W := residueClassWeight (m := m)) t u,
    polygonSqProfile_residueClassWeight_eq_H (m := m) (x := t - u)]

/-- The same concrete realization has distances given exactly by `G`. -/
theorem cyclicResiduePoint_dist_eq_G {m : Nat} [NeZero m] (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) =
        G (sepAngle (t - u)) := by
  calc
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
        (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u)
        =
          Real.sqrt
            (dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
              (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) ^ 2) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]
    _ = Real.sqrt (H (sepAngle (t - u))) := by
          rw [cyclicResiduePoint_dist_sq_eq_H (m := m) t u]
    _ = G (sepAngle (t - u)) := by
          rfl

/-- Inside a Singer difference set, equal distances in the concrete realization
already force the underlying unordered pairs to agree. -/
theorem eq_or_eq_swap_of_cyclicResiduePoint_dist_eq
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hEq :
      dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) =
      dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) c)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hprofile : cyclicProfileDist a b = cyclicProfileDist c d := by
    simpa [cyclicProfileDist, cyclicResiduePoint_dist_eq_G (m := m)] using hEq
  exact eq_or_eq_swap_of_cyclicProfileDist_eq (D := D) ha hb hc hd hab hprofile

end

end DiameterConstruction

