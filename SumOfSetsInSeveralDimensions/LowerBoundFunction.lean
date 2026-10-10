/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum.Basic

/-!
# The lower bound as a function of the dimension and the cardinalities

The lower bound in Ruzsa's theorem for sets `A` and `B` with `|A| = n ≥ |B| = m` and `A + B` of
affine dimension `d` is `sumsetCardLowerBound d m n = n + ∑ t ∈ Icc 1 (m - 1), min d (n - t)`.
The induction in the proof removes one point from `A`, from `B`, or from both, and the dimension
stays the same or drops by one. This file proves the inequality between the values of the bound
that each of these cases needs.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

/-- The candidate lower bound for the cardinality of a sumset of affine dimension `d`. -/
def sumsetCardLowerBound (d m n : ℕ) : ℕ :=
  n + (Finset.Icc 1 (m - 1)).sum fun t ↦ min d (n - t)

/-- The definition of `sumsetCardLowerBound`. -/
lemma sumsetCardLowerBound_eq (d m n : ℕ) :
    sumsetCardLowerBound d m n = n + (Finset.Icc 1 (m - 1)).sum (fun t ↦ min d (n - t)) := by
  rfl

private lemma Icc_two_eq_image_add_one (m : ℕ) :
    Finset.Icc 2 m = (Finset.Icc 1 (m - 1)).image (· + 1) := by
  ext t
  simp only [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro ht
    refine ⟨t - 1, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨u, hu, rfl⟩
    omega

private lemma sum_Icc_two_eq_sum_Icc_one (f : ℕ → ℕ) (m : ℕ) :
    (Finset.Icc 2 m).sum f = (Finset.Icc 1 (m - 1)).sum (fun t ↦ f (t + 1)) := by
  rw [Icc_two_eq_image_add_one, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.add_right_cancel hab

private lemma add_min_sub_one (d n : ℕ) :
    n + min d (n - 1) = n - 1 + min (d + 1) n := by
  omega

private lemma sumsetCardLowerBound_step {d m n : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m n = sumsetCardLowerBound d (m - 1) (n - 1) + min (d + 1) n := by
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, ← Finset.insert_Icc_add_one_left_eq_Icc]
  · rw [Finset.sum_insert]
    · norm_num only [Nat.reduceAdd]
      rw [sum_Icc_two_eq_sum_Icc_one]
      rw [← Nat.add_assoc, add_min_sub_one]
      simp only [Nat.add_assoc]
      apply congrArg (fun k => n - 1 + k)
      nth_rewrite 1 [add_comm (min (d + 1) n)]
      apply congrArg (fun k => k + min (d + 1) n)
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      omega
    · simp
  · omega

private lemma sumsetCardLowerBound_le_large_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) (n - 1) := by
  have hpred : Order.pred (m - 1) = m - 2 := by
    change Nat.pred (m - 1) = m - 2
    rw [Nat.pred_eq_sub_one]
    omega
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, ← Finset.insert_Icc_pred_right_eq_Icc]
  · rw [Finset.sum_insert]
    · rw [hpred]
      apply Nat.add_le_add
      · omega
      · refine le_trans (Nat.add_le_add (min_le_right d (n - (m - 1)))
          (Finset.sum_le_sum (g := fun t ↦ min (d - 1) (n - 1 - t) + 1)
            ?_)) ?_
        · intro t ht
          rw [Finset.mem_Icc] at ht
          omega
        · rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
          simp only [smul_eq_mul, mul_one]
          simp only [Nat.sub_sub, Nat.reduceAdd]
          omega
    · rw [Finset.mem_Icc]
      rw [hpred]
      omega
  · omega

private lemma sumsetCardLowerBound_mono_right (d m : ℕ) : Monotone (sumsetCardLowerBound d m) := by
  intro a b hab
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq]
  apply Nat.add_le_add hab
  apply Finset.sum_le_sum
  intro t _
  apply min_le_min_left
  omega

private lemma sumsetCardLowerBound_le_small_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) n := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm hmn)
  apply Nat.add_le_add_left
  apply sumsetCardLowerBound_mono_right
  omega

private lemma sumsetCardLowerBound_le_strict_right_deletion {d m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    sumsetCardLowerBound d m n ≤ m + sumsetCardLowerBound (d - 1) m (n - 1) := by
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq]
  apply le_trans (b := n + (Finset.Icc 1 (m - 1)).sum
    (fun t ↦ min (d - 1) (n - 1 - t) + 1))
  · apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Icc] at ht
    omega
  · rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
    simp only [smul_eq_mul, mul_one]
    omega

private lemma sumsetCardLowerBound_le_equal_right_deletion {d m : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m m ≤ m + sumsetCardLowerBound (d - 1) (m - 1) m := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm le_rfl)
  apply Nat.add_le_add_left
  apply sumsetCardLowerBound_mono_right
  omega

/-- The case in which one point is removed from each set and the dimension does not change: the
sumset loses at least `d + 1` points. -/
lemma sumsetCardLowerBound_of_full_case {d m n p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound d (m - 1) (n - 1) ≤ p) (hcard : p + d + 1 ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  rw [sumsetCardLowerBound_step hm]
  apply le_trans (Nat.add_le_add_right hrec _)
  apply le_trans (Nat.add_le_add_left (min_le_left (d + 1) n) _)
  omega

/-- The case in which one point is removed from each set and the dimension drops by one: the
sumset loses at least `n` points. -/
lemma sumsetCardLowerBound_of_large_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) (n - 1) ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm hmn)
  exact (Nat.add_le_add_left hrec n).trans hcard

/-- The case in which one point is removed from the smaller set and the dimension drops by one:
the sumset loses at least `n` points. -/
lemma sumsetCardLowerBound_of_small_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) n ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_small_deletion hm hmn)
  exact (Nat.add_le_add_left hrec n).trans hcard

/-- The case in which the sets have the same size `m`, one point is removed from one of them and
the dimension drops by one: the sumset loses at least `m` points. -/
lemma sumsetCardLowerBound_of_equal_right_case {d m p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) m ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m m ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_equal_right_deletion hm)
  exact (Nat.add_le_add_left hrec m).trans hcard

/-- The case in which one point is removed from the strictly larger set and the dimension drops
by one: the sumset loses at least `m` points. -/
lemma sumsetCardLowerBound_of_strict_right_case {d m n p s : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (hrec : sumsetCardLowerBound (d - 1) m (n - 1) ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_strict_right_deletion hm hmn)
  exact (Nat.add_le_add_left hrec m).trans hcard

end SumOfSetsInSeveralDimensions
