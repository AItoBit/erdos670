/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import Mathlib
import DiameterConstruction.Profile

/-!
# Euclidean realization of the cyclic profile

This file formalizes the weighted product-of-polygons construction from the paper.
For nonnegative weights `W_1, ..., W_N`, it defines the associated map into
`R^(2N)` and proves the exact squared-distance formula.
-/

namespace DiameterConstruction

open Real

noncomputable section

/-- The `r`-th polygon frequency, indexed from `1` rather than `0`. -/
def polygonFrequency {N : Nat} (r : Fin N) : Nat :=
  r.1 + 1

/-- The amplitude in the `r`-th two-dimensional factor. -/
def polygonAmplitude {N : Nat} (W : Fin N → NNReal) (r : Fin N) : Real :=
  Real.sqrt ((W r : Real) / 2)

/-- The finite weighted squared-distance profile attached to `W`. -/
def polygonSqProfile {N : Nat} (W : Fin N → NNReal) (theta : Real) : Real :=
  ∑ r : Fin N, (W r : Real) * (1 - Real.cos ((polygonFrequency r : Real) * theta))

/-- The weighted product-of-polygons realization at angle parameter `tau`. -/
def polygonPoint {N : Nat} (W : Fin N → NNReal) (tau : Real) :
    EuclideanSpace Real (Fin N × Fin 2) :=
  WithLp.toLp 2 fun p : Fin N × Fin 2 =>
    let amp := polygonAmplitude W p.1
    let theta := (polygonFrequency p.1 : Real) * tau
    if p.2 = 0 then amp * Real.cos theta else amp * Real.sin theta

/-- The same realization, sampled on the `m`-th roots of unity. -/
def cyclicPolygonPoint {N m : Nat} [NeZero m] (W : Fin N → NNReal) (t : ZMod m) :
    EuclideanSpace Real (Fin N × Fin 2) :=
  polygonPoint W (2 * Real.pi * (t.val : Real) / m)

/-- Reindex the `N` two-dimensional factors as a single `Fin (N * 2)` coordinate set. -/
def polygonPointReindex {N : Nat} :
    EuclideanSpace Real (Fin N × Fin 2) ≃ₗᵢ[Real] EuclideanSpace Real (Fin (N * 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real finProdFinEquiv

/-- The same weighted polygon realization, now viewed in `R^(2N)`. -/
def polygonPointFin {N : Nat} (W : Fin N → NNReal) (tau : Real) :
    EuclideanSpace Real (Fin (N * 2)) :=
  polygonPointReindex (polygonPoint W tau)

/-- The cyclic realization, now viewed in `R^(2N)`. -/
def cyclicPolygonPointFin {N m : Nat} [NeZero m] (W : Fin N → NNReal) (t : ZMod m) :
    EuclideanSpace Real (Fin (N * 2)) :=
  polygonPointReindex (cyclicPolygonPoint (m := m) W t)

@[simp] lemma polygonPoint_apply_zero {N : Nat} (W : Fin N → NNReal) (tau : Real) (r : Fin N) :
    polygonPoint W tau (r, 0) =
      polygonAmplitude W r * Real.cos ((polygonFrequency r : Real) * tau) := by
  simp [polygonPoint]

@[simp] lemma polygonPoint_apply_one {N : Nat} (W : Fin N → NNReal) (tau : Real) (r : Fin N) :
    polygonPoint W tau (r, 1) =
      polygonAmplitude W r * Real.sin ((polygonFrequency r : Real) * tau) := by
  simp [polygonPoint]

lemma real_dist_sq_eq_sq_sub (x y : Real) : dist x y ^ 2 = (x - y) ^ 2 := by
  rw [Real.dist_eq, sq_abs]

lemma two_coord_sq_sum (amp alpha beta : Real) :
    (amp * Real.cos alpha - amp * Real.cos beta) ^ 2 +
        (amp * Real.sin alpha - amp * Real.sin beta) ^ 2 =
      2 * amp ^ 2 * (1 - Real.cos (alpha - beta)) := by
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq alpha, Real.sin_sq_add_cos_sq beta]

lemma polygonAmplitude_sq {N : Nat} (W : Fin N → NNReal) (r : Fin N) :
    polygonAmplitude W r ^ 2 = (W r : Real) / 2 := by
  unfold polygonAmplitude
  have hnonneg : 0 ≤ ((W r : Real) / 2) := by
    exact div_nonneg (show 0 ≤ (W r : Real) by exact_mod_cast (W r).2) (by norm_num)
  exact Real.sq_sqrt hnonneg

lemma polygonPoint_factor_dist_sq {N : Nat} (W : Fin N → NNReal) (tau sigma : Real)
    (r : Fin N) :
    dist (polygonPoint W tau (r, 0)) (polygonPoint W sigma (r, 0)) ^ 2 +
        dist (polygonPoint W tau (r, 1)) (polygonPoint W sigma (r, 1)) ^ 2 =
      (W r : Real) * (1 - Real.cos ((polygonFrequency r : Real) * (tau - sigma))) := by
  rw [real_dist_sq_eq_sq_sub, real_dist_sq_eq_sq_sub]
  rw [polygonPoint_apply_zero, polygonPoint_apply_zero, polygonPoint_apply_one, polygonPoint_apply_one]
  rw [two_coord_sq_sum]
  rw [polygonAmplitude_sq]
  ring_nf

/-- Squared distances in the weighted polygon realization are given exactly by the
finite Fourier profile attached to the weights. -/
theorem polygonPoint_dist_sq {N : Nat} (W : Fin N → NNReal) (tau sigma : Real) :
    dist (polygonPoint W tau) (polygonPoint W sigma) ^ 2 =
      polygonSqProfile W (tau - sigma) := by
  rw [EuclideanSpace.dist_sq_eq, polygonSqProfile, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Fin.sum_univ_two]
  exact polygonPoint_factor_dist_sq W tau sigma r

/-- The same formula for the `m`-cyclic sampling of the construction. -/
theorem cyclicPolygonPoint_dist_sq {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) W t) (cyclicPolygonPoint (m := m) W u) ^ 2 =
      polygonSqProfile W
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) := by
  simpa [cyclicPolygonPoint] using
    polygonPoint_dist_sq W
      (2 * Real.pi * (t.val : Real) / m) (2 * Real.pi * (u.val : Real) / m)

lemma cos_mul_valMinAbs_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (r : ZMod m) :
    Real.cos ((f : Real) * (2 * Real.pi * (r.valMinAbs : Real) / m)) =
      Real.cos ((f : Real) * sepAngle r) := by
  by_cases hr : 0 ≤ r.valMinAbs
  · have hcast : ((r.valMinAbs.natAbs : Nat) : Real) = (r.valMinAbs : Real) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hr]
    rw [sepAngle, hcast]
  · have hr' : r.valMinAbs ≤ 0 := le_of_not_ge hr
    have hcast0 : ((r.valMinAbs.natAbs : Nat) : Real) = -(r.valMinAbs : Real) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hr', Int.cast_neg]
    have hcast : (r.valMinAbs : Real) = -((r.valMinAbs.natAbs : Nat) : Real) := by
      linarith
    rw [hcast, sepAngle]
    have hneg :
        (f : Real) * (2 * Real.pi * (-((r.valMinAbs.natAbs : Nat) : Real)) / m) =
          -((f : Real) * (2 * Real.pi * ((r.valMinAbs.natAbs : Nat) : Real) / m)) := by
      ring
    rw [hneg, Real.cos_neg]

lemma cos_mul_raw_sub_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (t u : ZMod m) :
    Real.cos ((f : Real) *
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m))) =
      Real.cos ((f : Real) * sepAngle (t - u)) := by
  let z : Int := (t - u).valMinAbs
  have hz : ((z : Int) : ZMod m) = t - u := by
    simp [z]
  have hzero : (((t.val : Int) - u.val - z : Int) : ZMod m) = 0 := by
    simp [Int.cast_sub, hz, z]
  have hdiv : (m : Int) ∣ ((t.val : Int) - u.val - z) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rcases hdiv with ⟨k, hk⟩
  have hkInt : (t.val : Int) - u.val = z + k * m := by
    linarith
  have hkReal : (t.val : Real) - (u.val : Real) = (z : Real) + k * m := by
    exact_mod_cast hkInt
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m)).ne'
  have hangle :
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) =
        2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi) := by
    calc
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m))
          = (2 * Real.pi) * ((t.val : Real) - (u.val : Real)) / m := by ring
      _ = (2 * Real.pi) * ((z : Real) + k * m) / m := by rw [hkReal]
      _ = 2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi) := by
        field_simp [hm0]
  have hmulcast : (f : Real) * (k : Real) = (((f : Int) * k : Int) : Real) := by
    exact_mod_cast (show (f : Int) * k = (f : Int) * k by rfl)
  calc
    Real.cos ((f : Real) *
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)))
        = Real.cos ((f : Real) * (2 * Real.pi * (z : Real) / m) +
            (((f : Int) * k : Int) : Real) * (2 * Real.pi)) := by
            rw [hangle]
            congr 1
            calc
              (f : Real) * (2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi))
                  = (f : Real) * (2 * Real.pi * (z : Real) / m) +
                      (f : Real) * ((k : Real) * (2 * Real.pi)) := by ring
              _ = (f : Real) * (2 * Real.pi * (z : Real) / m) +
                    (((f : Int) * k : Int) : Real) * (2 * Real.pi) := by
                    rw [show (f : Real) * ((k : Real) * (2 * Real.pi)) =
                        ((f : Real) * (k : Real)) * (2 * Real.pi) by ring, hmulcast]
    _ = Real.cos ((f : Real) * (2 * Real.pi * (z : Real) / m)) := by
      rw [Real.cos_add_int_mul_two_pi]
    _ = Real.cos ((f : Real) * sepAngle (t - u)) := by
      simpa [z] using cos_mul_valMinAbs_eq_cos_mul_sepAngle (m := m) f (t - u)

lemma polygonSqProfile_eq_sepAngle {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    polygonSqProfile W
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) =
      polygonSqProfile W (sepAngle (t - u)) := by
  unfold polygonSqProfile
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [cos_mul_raw_sub_eq_cos_mul_sepAngle (m := m) (f := polygonFrequency r) t u]

/-- The cyclic realization depends only on the intrinsic cyclic separation angle. -/
theorem cyclicPolygonPoint_dist_sq_eq_profile {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) W t) (cyclicPolygonPoint (m := m) W u) ^ 2 =
      polygonSqProfile W (sepAngle (t - u)) := by
  rw [cyclicPolygonPoint_dist_sq (m := m) W t u, polygonSqProfile_eq_sepAngle (m := m) W t u]

/-- Reindexing the coordinates into `Fin (N * 2)` preserves the same squared-distance formula. -/
theorem polygonPointFin_dist_sq {N : Nat} (W : Fin N → NNReal) (tau sigma : Real) :
    dist (polygonPointFin W tau) (polygonPointFin W sigma) ^ 2 =
      polygonSqProfile W (tau - sigma) := by
  rw [polygonPointFin, ← polygonPoint_dist_sq W tau sigma]
  exact congrArg (fun x : Real => x ^ 2) (polygonPointReindex.dist_map _ _)

/-- The cyclic `R^(2N)` realization satisfies the same formula. -/
theorem cyclicPolygonPointFin_dist_sq {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    dist (cyclicPolygonPointFin (m := m) W t) (cyclicPolygonPointFin (m := m) W u) ^ 2 =
      polygonSqProfile W
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) := by
  rw [cyclicPolygonPointFin, ← cyclicPolygonPoint_dist_sq (m := m) W t u]
  exact congrArg (fun x : Real => x ^ 2) (polygonPointReindex.dist_map _ _)

end

end DiameterConstruction

