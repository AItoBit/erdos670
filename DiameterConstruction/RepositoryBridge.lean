/-
Copyright 2026 The Formal Conjectures Authors.
Released under the MIT license, as described in the file LICENSE.
-/
module

public import DiameterConstruction.MainTheorem
public import Mathlib.Data.Sym.Sym2

/-!
# The Formal Conjectures formulation of Ho's counterexample

This file converts Boon Suan Ho's infinite-family theorem into the finite-set
formulation used by `Erdos670` in google-deepmind/formal-conjectures.
The fixed-dimension conjecture is not addressed.

References:
* https://arxiv.org/abs/2604.15305
* https://github.com/google-deepmind/formal-conjectures/blob/e87ec728e936c3a42ab1d6dc26ee7854134a2949/FormalConjectures/ErdosProblems/670.lean
-/

@[expose] public section

namespace Erdos670

open Filter

/-- Distances of different unordered pairs of distinct points are at least one apart. -/
def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/-- Ho's growing-dimension counterexamples, in the repository's exact formulation. -/
theorem erdos_670.variants.ho :
    ∀ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin (n ^ 2 - n))), A.card = n ∧
        HasSeparatedDistances A ∧
        Metric.diam (A : Set (EuclideanSpace ℝ (Fin (n ^ 2 - n)))) ≤
          (1 - 1 / Real.pi ^ 2 + ε) * (n : ℝ) ^ 2 := by
  classical
  intro ε hε
  obtain ⟨err, herr, hfamily⟩ :=
    DiameterConstruction.infinitely_many_quantitative_counterexamples
  have hevent : ∀ᶠ q in atTop, err q < ε :=
    herr.eventually (gt_mem_nhds hε)
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hevent
  rw [frequently_atTop]
  intro N
  obtain ⟨q, hq, _, D, p, hinj, hsep, hdiam⟩ := hfamily (max N Q)
  refine ⟨q + 1, by omega, D.carrier.image p, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, D.card_eq]
  · intro a ha b hb c hc e he hab hce hpairs
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    apply hsep ha' hb' hc' he'
    · exact fun h => hab (congrArg p h)
    · exact fun h => hce (congrArg p h)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hpairs rfl
      · exact hpairs (Sym2.eq_swap)
  · have hsmall : err q ≤ ε := (hQ q (by omega)).le
    have hbound := hdiam.trans (mul_le_mul_of_nonneg_right
      (add_le_add_right hsmall DiameterConstruction.cStar) (sq_nonneg (q + 1 : ℝ)))
    simpa [Finset.coe_image, DiameterConstruction.cStar, Nat.cast_add, Nat.cast_one]
      using hbound

/-- The asymptotic lower bound cannot hold uniformly in the dimension. -/
theorem erdos_670.variants.uniform_in_dim :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  intro h
  have hε : 0 < 1 / (4 * Real.pi ^ 2) := by positivity
  have hupper := erdos_670.variants.ho _ hε
  have hlower := h _ hε
  obtain ⟨n, ⟨A, hcard, hsep, hdiam⟩, hn⟩ :=
    (hupper.and_eventually (hlower.and (eventually_ge_atTop 1))).exists
  have hlow := hn.1 _ A hcard hsep
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.2
  have hgap : 0 < 1 / Real.pi ^ 2 := by positivity
  have heq : 1 / (4 * Real.pi ^ 2) = (1 / Real.pi ^ 2) / 4 := by ring
  rw [heq] at hlow hdiam
  nlinarith [mul_pos hgap (sq_pos_of_pos hnpos)]

end Erdos670
