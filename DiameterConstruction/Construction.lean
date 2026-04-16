/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/
import DiameterConstruction.Singer
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Combinatorial consequences of Singer difference sets

This file isolates the paper's finite combinatorial step: in a Singer difference set,
unordered pairs are indexed by the cyclic separation `s = 1, ..., (m-1)/2`.
-/

namespace DiameterConstruction

open ZMod

section SingerPairs

variable {m n : ℕ} [NeZero m] (D : SingerDiffSet m n)

omit [NeZero m] in
lemma sub_ne_zero_of_ne {a b : ZMod m} (h : a ≠ b) : a - b ≠ 0 := by
  intro hsub
  exact h (sub_eq_zero.mp hsub)

/-- In a Singer difference set, two ordered pairs with the same nonzero difference coincide. -/
lemma ordered_pair_eq_of_sub_eq
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hsub : a - b = c - d) :
    a = c ∧ b = d := by
  let r : ZMod m := a - b
  have hr0 : r ≠ 0 := sub_ne_zero_of_ne hab
  obtain ⟨p, hp, hpuniq⟩ := D.diff_unique r hr0
  have habp : (a, b) = p := by
    apply hpuniq
    exact ⟨ha, hb, by simp [r]⟩
  have hcdp : (c, d) = p := by
    apply hpuniq
    exact ⟨hc, hd, by simpa [r] using hsub.symm⟩
  have hpair : (a, b) = (c, d) := habp.trans hcdp.symm
  simpa [Prod.mk.injEq] using hpair

/-- Equal absolute cyclic separations force equality up to swapping the pair. -/
lemma eq_or_eq_swap_of_natAbs_sub_eq
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hsep : (a - b).valMinAbs.natAbs = (c - d).valMinAbs.natAbs) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases (ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs (a := a - b) (b := c - d)).mp hsep with h | h
  · exact Or.inl <| ordered_pair_eq_of_sub_eq (D := D) ha hb hc hd hab h
  · have hswap : a - b = d - c := by
      simpa using h
    exact Or.inr <| ordered_pair_eq_of_sub_eq (D := D) ha hb hd hc hab hswap

end SingerPairs

end DiameterConstruction

