/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Trace.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Singer difference sets

This file formalizes Singer's theorem: for every prime power `q`, there exists a cyclic
`(q^2 + q + 1, q + 1, 1)` difference set in `ZMod (q^2 + q + 1)`.

The construction follows the finite-field proof via the trace-zero hyperplane in a cubic
extension and transports the resulting cyclic quotient back to `ZMod`.
-/

namespace DiameterConstruction

open Finset ZMod
open scoped LinearAlgebra.Projectivization

/-- A cyclic `(m, n, 1)` difference set in `ZMod m`: a subset of size `n` such that every
nonzero residue has a unique representation as a difference of two elements. -/
structure SingerDiffSet (m : ℕ) [NeZero m] (n : ℕ) where
  carrier : Finset (ZMod m)
  card_eq : carrier.card = n
  diff_unique : ∀ r : ZMod m, r ≠ 0 →
    ∃! p : ZMod m × ZMod m, p.1 ∈ carrier ∧ p.2 ∈ carrier ∧ p.1 - p.2 = r

noncomputable section

namespace SingerConstruction

section ProjectiveSubtype

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projectivizationSubtypeTo (s : Submodule K V) :
    ℙ K s → {x : ℙ K V // x ∈ s.projectivization} := fun x =>
  ⟨Projectivization.map s.subtype Subtype.val_injective x, by
    induction x using Projectivization.ind with
    | h v hv =>
        simp [Projectivization.map_mk, Submodule.mk_mem_projectivization_iff]⟩

def projectivizationSubtypeInv (s : Submodule K V) :
    {x : ℙ K V // x ∈ s.projectivization} → ℙ K s := fun x =>
  have hxmem : x.1.rep ∈ s := by
    have hxmk : Projectivization.mk K x.1.rep x.1.rep_nonzero ∈ s.projectivization := by
      simp [x.1.mk_rep, x.2]
    exact (Submodule.mk_mem_projectivization_iff s x.1.rep_nonzero).1 hxmk
  Projectivization.mk K (⟨x.1.rep, hxmem⟩ : s) (by simpa using x.1.rep_nonzero)

def projectivizationSubtypeEquiv (s : Submodule K V) :
    ℙ K s ≃ {x : ℙ K V // x ∈ s.projectivization} where
  toFun := projectivizationSubtypeTo s
  invFun := projectivizationSubtypeInv s
  left_inv x := by
    induction x using Projectivization.ind with
    | h v hv =>
        change
          Projectivization.mk K
              (⟨(Projectivization.mk K (v : V) (by simpa using hv)).rep, ?_⟩ : s) _ =
            Projectivization.mk K v hv
        rw [Projectivization.mk_eq_mk_iff' K]
        obtain ⟨a, ha⟩ :=
          Projectivization.exists_smul_eq_mk_rep (K := K) (V := V) (v := (v : V))
            (by simpa using hv)
        refine ⟨a, Subtype.ext ?_⟩
        simpa [Projectivization.map_mk] using ha
  right_inv x := by
    apply Subtype.ext
    change
      Projectivization.map s.subtype Subtype.val_injective
          (Projectivization.mk K (⟨x.1.rep, ?_⟩ : s) _) = x.1
    rw [Projectivization.map_mk]
    exact x.1.mk_rep

end ProjectiveSubtype

variable (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)

local notation "K" => GaloisField p n
local notation "q" => Nat.card K
local notation "L" => FiniteField.Extension K p 3

def scalarSubgroup : Subgroup Lˣ :=
  (Units.map ((algebraMap K L) : K →* L)).range

local notation "S" => scalarSubgroup p n
local notation "Q" => Lˣ ⧸ S

def projToQuotient : ℙ K L → Q :=
  Projectivization.lift
    (fun v => QuotientGroup.mk (Units.mk0 (v : L) v.2))
    (by
      intro a b t h
      have ht : t ≠ 0 := by
        intro ht0
        apply a.2
        simp [h, ht0]
      apply QuotientGroup.eq.mpr
      refine ⟨(Units.mk0 t ht)⁻¹, ?_⟩
      ext
      simp [h, Algebra.smul_def, mul_assoc])

def quotientToProj : Q → ℙ K L := by
  refine Quotient.lift (fun u : Lˣ => Projectivization.mk K (u : L) u.ne_zero) ?_
  intro u v huv
  change QuotientGroup.leftRel S u v at huv
  rw [QuotientGroup.leftRel_apply] at huv
  rw [Projectivization.mk_eq_mk_iff' K (u : L) (v : L) u.ne_zero v.ne_zero]
  rcases huv with ⟨c, hc⟩
  refine ⟨((c⁻¹ : Kˣ) : K), ?_⟩
  have hc' : (((Units.map ((algebraMap K L) : K →* L)) c : Lˣ) : L) = (u : L)⁻¹ * (v : L) := by
    simpa using congrArg (fun z : Lˣ => (z : L)) hc
  calc
    (((c⁻¹ : Kˣ) : K) • (v : L)) =
        ((((Units.map ((algebraMap K L) : K →* L)) c)⁻¹ : Lˣ) : L) * v := by
      simp [Algebra.smul_def]
    _ = (((v : L)⁻¹ * (v : L)) * (u : L)) := by
      simp [hc', mul_comm]
    _ = u := by
      simp [Units.ne_zero v]

theorem left_inv_projToQuotient :
    Function.LeftInverse (quotientToProj p n) (projToQuotient p n) := by
  intro x
  induction x using Projectivization.ind with
  | h v hv =>
      simp [projToQuotient, quotientToProj]

theorem right_inv_projToQuotient :
    Function.RightInverse (quotientToProj p n) (projToQuotient p n) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro u
  simp [quotientToProj, projToQuotient]

def projEquivQuotient : ℙ K L ≃ Q where
  toFun := projToQuotient p n
  invFun := quotientToProj p n
  left_inv := left_inv_projToQuotient p n
  right_inv := right_inv_projToQuotient p n

def traceHyperplane : Submodule K L :=
  (Algebra.trace K L).ker

theorem finrank_traceHyperplane :
    Module.finrank K (traceHyperplane p n) = 2 := by
  have hrange : LinearMap.range (Algebra.trace K L) = ⊤ := by
    exact LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)
  have hs := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  rw [hrange, finrank_top] at hs
  have hs' : 1 + Module.finrank K ((Algebra.trace K L).ker) = 3 := by
    simpa [FiniteField.finrank_extension K p 3, add_comm, add_left_comm, add_assoc] using hs
  have hs'' : Module.finrank K ((Algebra.trace K L).ker) = 2 := by omega
  simpa [traceHyperplane] using hs''

def traceZeroRestriction (u : Lˣ) : traceHyperplane p n →ₗ[K] K where
  toFun x := Algebra.trace K L ((u : L) * x.1)
  map_add' x y := by
    simp [mul_add]
  map_smul' c x := by
    change Algebra.trace K L ((u : L) * (c • x.1)) = c * Algebra.trace K L ((u : L) * x.1)
    rw [show (u : L) * (c • x.1) = c • ((u : L) * x.1) by
      simp [Algebra.smul_def, mul_assoc, mul_comm]]
    exact (Algebra.trace K L).map_smul c _

theorem traceZeroRestriction_ne_zero {u : Lˣ} (hu : (u : Q) ≠ 1) :
    traceZeroRestriction p n u ≠ 0 := by
  intro hzero
  obtain ⟨y, hy⟩ := (Algebra.trace_surjective K L) 1
  let c : K := Algebra.trace K L ((u : L) * y)
  have hall : ∀ x : L, Algebra.traceForm K L ((u : L) - algebraMap K L c) x = 0 := by
    intro x
    let z : L := x - Algebra.trace K L x • y
    have hzmem : z ∈ traceHyperplane p n := by
      show Algebra.trace K L z = 0
      simp [z, hy]
    have hz0 : Algebra.trace K L ((u : L) * z) = 0 := by
      have hz := LinearMap.congr_fun hzero ⟨z, hzmem⟩
      simpa [traceZeroRestriction] using hz
    have hz2 : Algebra.trace K L ((u : L) * x) - Algebra.trace K L x * c = 0 := by
      rw [show (u : L) * z = (u : L) * x - ((Algebra.trace K L x : K) • ((u : L) * y)) by
        simp [z, mul_sub, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]] at hz0
      rw [LinearMap.map_sub] at hz0
      simpa [c] using hz0
    have htrace_scalar : Algebra.trace K L ((algebraMap K L c) * x) = c * Algebra.trace K L x := by
      rw [show (algebraMap K L c) * x = c • x by simp [Algebra.smul_def]]
      exact (Algebra.trace K L).map_smul c x
    have hform0 :
        Algebra.traceForm K L ((u : L) - algebraMap K L c) x =
          Algebra.trace K L ((u : L) * x) - c * Algebra.trace K L x := by
      rw [Algebra.traceForm_apply, sub_mul, LinearMap.map_sub, htrace_scalar]
    have hform :
        Algebra.traceForm K L ((u : L) - algebraMap K L c) x =
          Algebra.trace K L ((u : L) * x) - Algebra.trace K L x * c := by
      simpa [mul_comm] using hform0
    exact hform.trans hz2
  have hker : ((u : L) - algebraMap K L c) ∈ LinearMap.ker (Algebra.traceForm K L) := by
    show Algebra.traceForm K L ((u : L) - algebraMap K L c) = 0
    ext x
    exact hall x
  have hscalar : (u : L) - algebraMap K L c = 0 := by
    simpa [(traceForm_nondegenerate K L).ker_eq_bot] using hker
  have hu_eq : (u : L) = algebraMap K L c := sub_eq_zero.mp hscalar
  have hc0 : c ≠ 0 := by
    intro hc
    have hu0 : (u : L) = 0 := by
      simp [hu_eq, hc]
    exact u.ne_zero hu0
  have hu_mem : u ∈ S := by
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext
    simp [hu_eq]
  exact hu <| (QuotientGroup.eq_one_iff u).2 hu_mem

def projectivizationSubtypeMap (s : Submodule K L) : ℙ K s → ℙ K L :=
  fun x => (projectivizationSubtypeTo s x).1

def mulLinearEquiv (u : Lˣ) : L ≃ₗ[K] L where
  toFun x := (u : L) * x
  invFun x := ((u⁻¹ : Lˣ) : L) * x
  left_inv x := by
    simp
  right_inv x := by
    simp
  map_add' x y := by
    simp [mul_add]
  map_smul' c x := by
    simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]

def projMul (u : Lˣ) : ℙ K L → ℙ K L :=
  Projectivization.map (mulLinearEquiv p n u).toLinearMap (mulLinearEquiv p n u).injective

theorem quotientToProj_mul (u : Lˣ) (d : Q) :
    quotientToProj p n ((u : Q) * d) = projMul p n u (quotientToProj p n d) := by
  refine QuotientGroup.induction_on d ?_
  intro v
  change quotientToProj p n ((u * v : Lˣ) : Q) =
    projMul p n u (quotientToProj p n (v : Q))
  rfl

def singerSet : Set Q :=
  {d | quotientToProj p n d ∈ (traceHyperplane p n).projectivization}

def quotientSubtypeEquiv (s : Set (ℙ K L)) :
    {d : Q // quotientToProj p n d ∈ s} ≃ {x : ℙ K L // x ∈ s} where
  toFun d := ⟨quotientToProj p n d.1, d.2⟩
  invFun x := ⟨projToQuotient p n x.1, by
    rw [left_inv_projToQuotient p n x.1]
    exact x.2⟩
  left_inv d := by
    apply Subtype.ext
    exact right_inv_projToQuotient p n d.1
  right_inv x := by
    apply Subtype.ext
    exact left_inv_projToQuotient p n x.1

def singerSubtypeEquivProjectivization :
    {d : Q // d ∈ singerSet p n} ≃ ℙ K (traceHyperplane p n) :=
  (quotientSubtypeEquiv p n ((traceHyperplane p n).projectivization.carrier)).trans
    (projectivizationSubtypeEquiv (traceHyperplane p n)).symm

theorem singerSet_card :
    Nat.card {d : Q // d ∈ singerSet p n} = q + 1 := by
  exact Nat.card_congr (singerSubtypeEquivProjectivization p n)
    |>.trans <| by
      simpa [finrank_traceHyperplane p n] using
        Projectivization.card_of_finrank_two K (traceHyperplane p n)
          (finrank_traceHyperplane p n)

theorem quotient_isCyclic : IsCyclic Q := by
  exact isCyclic_of_surjective (QuotientGroup.mk' S) QuotientGroup.mk_surjective

theorem quotient_card :
    Nat.card Q = q ^ 2 + q + 1 := by
  exact Nat.card_congr (projEquivQuotient p n).symm
    |>.trans <| by
      simpa [FiniteField.finrank_extension K p 3, pow_succ, pow_zero, Finset.sum_range_succ,
        Finset.sum_range_one, add_assoc, add_left_comm, add_comm, one_mul, mul_comm,
        mul_left_comm, mul_assoc] using
        Projectivization.card_of_finrank K L (FiniteField.finrank_extension K p 3)

def tracePointCondition (u : Lˣ) (x : ℙ K (traceHyperplane p n)) : Prop :=
  projMul p n u (projectivizationSubtypeMap p n (traceHyperplane p n) x) ∈
    (traceHyperplane p n).projectivization

theorem tracePointCondition_iff (u : Lˣ) (x : ℙ K (traceHyperplane p n)) :
    tracePointCondition p n u x ↔
      x ∈ (LinearMap.ker (traceZeroRestriction p n u)).projectivization := by
  induction x using Projectivization.ind with
  | h v hv =>
      change
        Projectivization.mk K ((u : L) * (v : traceHyperplane p n)) ?_ ∈
            (traceHyperplane p n).projectivization ↔
          Projectivization.mk K v hv ∈
            (LinearMap.ker (traceZeroRestriction p n u)).projectivization
      rw [Submodule.mk_mem_projectivization_iff, Submodule.mk_mem_projectivization_iff]
      change ((u : L) * (v : L)) ∈ traceHyperplane p n ↔ traceZeroRestriction p n u v = 0
      simp [traceHyperplane, traceZeroRestriction]

def localIntersectionToTracePoints (u : Lˣ) :
    {d : Q // d ∈ singerSet p n ∧ (u : Q) * d ∈ singerSet p n} ≃
      {x : ℙ K (traceHyperplane p n) // tracePointCondition p n u x} where
  toFun d := by
    let y :
        {x : ℙ K L // x ∈ (traceHyperplane p n).projectivization} :=
      ⟨quotientToProj p n d.1, d.2.1⟩
    refine ⟨(projectivizationSubtypeEquiv (traceHyperplane p n)).symm y, ?_⟩
    have hy :
        projectivizationSubtypeMap p n (traceHyperplane p n)
            ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm y) =
          quotientToProj p n d.1 := by
      exact congrArg Subtype.val
        ((projectivizationSubtypeEquiv (traceHyperplane p n)).apply_symm_apply y)
    rw [tracePointCondition, hy]
    simpa [singerSet, quotientToProj_mul p n u d.1] using d.2.2
  invFun x := by
    refine ⟨projToQuotient p n (projectivizationSubtypeMap p n (traceHyperplane p n) x.1), ?_⟩
    constructor
    · change quotientToProj p n
          (projToQuotient p n (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) ∈
            (traceHyperplane p n).projectivization
      rw [left_inv_projToQuotient p n]
      change (projectivizationSubtypeTo (traceHyperplane p n) x.1).1 ∈
          (traceHyperplane p n).projectivization
      exact (projectivizationSubtypeTo (traceHyperplane p n) x.1).2
    · change quotientToProj p n
          ((u : Q) * projToQuotient p n
            (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) ∈
            (traceHyperplane p n).projectivization
      rw [quotientToProj_mul p n u]
      simpa [left_inv_projToQuotient p n
          (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)] using x.2
  left_inv d := by
    apply Subtype.ext
    change
      projToQuotient p n
        (projectivizationSubtypeMap p n (traceHyperplane p n)
          ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm
            ⟨quotientToProj p n d.1, d.2.1⟩)) = d.1
    have :
        projectivizationSubtypeMap p n (traceHyperplane p n)
            ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm
              ⟨quotientToProj p n d.1, d.2.1⟩) =
          quotientToProj p n d.1 := by
      exact congrArg Subtype.val
        ((projectivizationSubtypeEquiv (traceHyperplane p n)).apply_symm_apply
          ⟨quotientToProj p n d.1, d.2.1⟩)
    simpa [this] using right_inv_projToQuotient p n d.1
  right_inv x := by
    apply Subtype.ext
    change
      (projectivizationSubtypeEquiv (traceHyperplane p n)).symm
          ⟨quotientToProj p n
            (projToQuotient p n
              (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)),
            ?_⟩ = x.1
    have hx :
        quotientToProj p n
            (projToQuotient p n
              (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) =
          projectivizationSubtypeMap p n (traceHyperplane p n) x.1 := by
      exact left_inv_projToQuotient p n
        (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)
    have hx' :
        (projectivizationSubtypeEquiv (traceHyperplane p n)).symm
            ⟨projectivizationSubtypeMap p n (traceHyperplane p n) x.1,
              (projectivizationSubtypeTo (traceHyperplane p n) x.1).2⟩ = x.1 := by
      exact (projectivizationSubtypeEquiv (traceHyperplane p n)).symm_apply_apply x.1
    simpa [hx] using hx'

def localIntersectionEquivKernel (u : Lˣ) :
    {d : Q // d ∈ singerSet p n ∧ (u : Q) * d ∈ singerSet p n} ≃
      ℙ K (LinearMap.ker (traceZeroRestriction p n u)) :=
  (localIntersectionToTracePoints p n u).trans <|
    (Equiv.subtypeEquivRight fun x => tracePointCondition_iff p n u x).trans
      (projectivizationSubtypeEquiv (LinearMap.ker (traceZeroRestriction p n u))).symm

theorem finrank_traceZeroRestriction_ker {u : Lˣ} (hu : (u : Q) ≠ 1) :
    Module.finrank K (LinearMap.ker (traceZeroRestriction p n u)) = 1 := by
  have hsurj : Function.Surjective (traceZeroRestriction p n u) := by
    have hK : Module.finrank K K = 1 := by simp
    exact surjective_of_nonzero_of_finrank_eq_one
      hK (f := traceZeroRestriction p n u)
      (traceZeroRestriction_ne_zero p n hu)
  have hrange : LinearMap.range (traceZeroRestriction p n u) = ⊤ := by
    exact LinearMap.range_eq_top.mpr hsurj
  have hs := LinearMap.finrank_range_add_finrank_ker (traceZeroRestriction p n u)
  rw [hrange, finrank_top, finrank_traceHyperplane p n] at hs
  have hs' : 1 + Module.finrank K (LinearMap.ker (traceZeroRestriction p n u)) = 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using hs
  omega

theorem localIntersection_card {u : Lˣ} (hu : (u : Q) ≠ 1) :
    Nat.card {d : Q // d ∈ singerSet p n ∧ (u : Q) * d ∈ singerSet p n} = 1 := by
  refine Nat.card_congr (localIntersectionEquivKernel p n u) |>.trans ?_
  simpa [finrank_traceZeroRestriction_ker p n hu] using
    Projectivization.card_of_finrank K
      (LinearMap.ker (traceZeroRestriction p n u))
      (finrank_traceZeroRestriction_ker p n hu)

theorem singerSet_translate_unique_aux {u : Lˣ} (hu : (u : Q) ≠ 1) :
    ∃! d : Q, d ∈ singerSet p n ∧ (u : Q) * d ∈ singerSet p n := by
  let A := {d : Q // d ∈ singerSet p n ∧ (u : Q) * d ∈ singerSet p n}
  have hA : Nat.card A = 1 := localIntersection_card p n hu
  have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA).1
  let a : A := Classical.choice ((Nat.card_eq_one_iff_unique.mp hA).2)
  refine ⟨a.1, a.2, ?_⟩
  intro d hd
  have : (⟨d, hd⟩ : A) = a := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

theorem singerSet_translate_unique (g : Q) (hg : g ≠ 1) :
    ∃! d : Q, d ∈ singerSet p n ∧ g * d ∈ singerSet p n := by
  refine QuotientGroup.induction_on g ?_ hg
  intro u hu
  exact singerSet_translate_unique_aux p n hu

lemma unique_translate_to_unique_difference
    {A : Type*} [AddCommGroup A] {D : Set A}
    (h : ∀ x : A, x ≠ 0 → ∃! b : A, b ∈ D ∧ x + b ∈ D) :
    ∀ x : A, x ≠ 0 →
      ∃! p : A × A, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 - p.2 = x := by
  intro x hx
  rcases h x hx with ⟨b, hb, hb_unique⟩
  refine ⟨(x + b, b), ?_, ?_⟩
  · refine ⟨hb.2, hb.1, ?_⟩
    simp [sub_eq_add_neg, add_assoc]
  · intro p hp
    have hpb : p.2 ∈ D ∧ x + p.2 ∈ D := by
      refine ⟨hp.2.1, ?_⟩
      have hxpb : x + p.2 = p.1 := by
        calc
          x + p.2 = (p.1 - p.2) + p.2 := by rw [hp.2.2]
          _ = p.1 := by
            simp [sub_eq_add_neg, add_assoc]
      simpa [hxpb] using hp.1
    have hp2 : p.2 = b := hb_unique _ hpb
    have hp1 : p.1 = x + b := by
      calc
        p.1 = x + p.2 := by
          have hxpb : x + p.2 = p.1 := by
            calc
              x + p.2 = (p.1 - p.2) + p.2 := by rw [hp.2.2]
              _ = p.1 := by
                simp [sub_eq_add_neg, add_assoc]
          exact hxpb.symm
        _ = x + b := by rw [hp2]
    ext <;> simp [hp1, hp2]

theorem singer_exists_zmod :
    let m := q ^ 2 + q + 1
    ∃ D : Finset (ZMod m), D.card = q + 1 ∧
      ∀ r : ZMod m, r ≠ 0 →
        ∃! p : ZMod m × ZMod m, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 - p.2 = r := by
  classical
  let m : ℕ := q ^ 2 + q + 1
  have hQm : Nat.card Q = m := quotient_card p n
  let e : Multiplicative (ZMod m) ≃* Q :=
    hQm ▸ zmodCyclicMulEquiv (G := Q) (quotient_isCyclic p n)
  let f : ZMod m ≃ Q := Multiplicative.ofAdd.trans e.toEquiv
  let Dset : Set (ZMod m) := {x | f x ∈ singerSet p n}
  have hDcard : Nat.card {x : ZMod m // x ∈ Dset} = q + 1 := by
    simpa [Dset] using
      (Nat.card_congr ((f).subtypeEquiv fun x => Iff.rfl)).trans (singerSet_card p n)
  have htranslate :
      ∀ x : ZMod m, x ≠ 0 → ∃! b : ZMod m, b ∈ Dset ∧ x + b ∈ Dset := by
    intro x hx
    have hg : f x ≠ 1 := by
      intro hx1
      apply hx
      apply Multiplicative.ofAdd.injective
      apply e.injective
      simpa [f] using hx1
    rcases singerSet_translate_unique p n (f x) hg with ⟨d, hd, hd_unique⟩
    let b : ZMod m := (e.symm d).toAdd
    refine ⟨b, ?_, ?_⟩
    · constructor
      · change f ((e.symm d).toAdd) ∈ singerSet p n
        simpa [f] using hd.1
      · change f (x + (e.symm d).toAdd) ∈ singerSet p n
        change e (Multiplicative.ofAdd (x + (e.symm d).toAdd)) ∈ singerSet p n
        rw [show Multiplicative.ofAdd (x + (e.symm d).toAdd) =
            Multiplicative.ofAdd x * e.symm d by simp]
        simpa [f] using hd.2
    · intro b' hb'
      apply f.injective
      have hb'' : f b' ∈ singerSet p n ∧ f x * f b' ∈ singerSet p n := by
        refine ⟨hb'.1, ?_⟩
        have hxadd : f (x + b') = f x * f b' := by
          change e (Multiplicative.ofAdd (x + b')) = _
          rw [show Multiplicative.ofAdd (x + b') =
              Multiplicative.ofAdd x * Multiplicative.ofAdd b' by simp]
          simp [f]
        simpa [Dset, hxadd] using hb'.2
      have : f b' = d := hd_unique _ hb''
      simpa [b, f] using this
  let D : Finset (ZMod m) := (Set.toFinite Dset).toFinset
  refine ⟨D, ?_, ?_⟩
  · have hfin : Dset.Finite := Set.toFinite Dset
    calc
      D.card = Fintype.card {x : ZMod m // x ∈ Dset} := by
        simpa [D] using hfin.card_toFinset
      _ = q + 1 := by rwa [← Nat.card_eq_fintype_card]
  · intro r hr
    simpa [D, Dset, Set.mem_toFinset] using
      unique_translate_to_unique_difference (A := ZMod m) (D := Dset) htranslate r hr

end SingerConstruction

theorem singer_exists_prime_power (p n : ℕ) [Fact p.Prime] (_hn : n ≠ 0) :
    let q := Nat.card (GaloisField p n)
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq : 0 < q := Nat.card_pos
      omega⟩
    Nonempty (SingerDiffSet m (q + 1)) := by
  classical
  dsimp
  obtain ⟨D, hcard, hdiff⟩ := SingerConstruction.singer_exists_zmod (p := p) (n := n)
  refine ⟨{ carrier := D, card_eq := hcard, diff_unique := ?_ }⟩
  intro r hr
  exact hdiff r hr

/-- Singer's theorem: every prime power `q` yields a cyclic
`(q^2 + q + 1, q + 1, 1)` difference set in `ZMod (q^2 + q + 1)`. -/
theorem singer_exists {q : ℕ} (hq : IsPrimePow q) :
    letI m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by omega⟩
    Nonempty (SingerDiffSet m (q + 1)) := by
  classical
  rcases (isPrimePow_nat_iff q).1 hq with ⟨p, n, hp, hnpos, hqpow⟩
  letI : Fact p.Prime := ⟨hp⟩
  let hn : n ≠ 0 := Nat.ne_of_gt hnpos
  simpa [GaloisField.card (p := p) (n := n) hn, hqpow] using
    singer_exists_prime_power (p := p) (n := n) hn

end

end DiameterConstruction

