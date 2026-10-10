/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import SumOfSetsInSeveralDimensions.GeometricDeletion
import SumOfSetsInSeveralDimensions.LowerBoundFunction
import SumOfSetsInSeveralDimensions.Normalize
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sum of sets in several dimensions

Ruzsa's theorem, from *Sum of sets in several dimensions*, Combinatorica 14 (1994): if
`A, B ⊆ ℝ^D` are finite sets with `B` nonempty and `|B| ≤ |A|`, and `A + B` has affine dimension
`d`, then `|A + B| ≥ |A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t)`.

The proof is by induction on `|A| + |B|`. Both sets are translated so that their
lexicographically least element is `0`. If `|B| ≥ 2`, the lemma `geometric_deletion_cases` removes
`0` from one or both of the sets, and the inequalities of `LowerBoundFunction.lean` compare the
bound for the smaller sets with the bound for `A` and `B`.

## Main statements

* `card_add_sum_min_le_card_add`: Ruzsa's theorem.
* `card_add_sum_min_le_card_add_of_le`: the same bound for every `d` at most the affine dimension
  of `A + B`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

private lemma two_le_card_of_nonempty_ne_one {α : Type*} (S : Finset α)
    (hS : S.Nonempty) (hcard : S.card ≠ 1) : 2 ≤ S.card := by
  rw [← Finset.card_pos] at hS
  omega

private lemma card_erase_add_card_erase_lt {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} {s : α} {t : β} {n : ℕ}
    (hs : s ∈ S) (ht : t ∈ T) (hn : S.card + T.card = n) :
    (S.erase s).card + (T.erase t).card < n := by
  rw [Finset.card_erase_of_mem hs, Finset.card_erase_of_mem ht, ← hn]
  suffices 0 < S.card ∧ 0 < T.card by omega
  exact ⟨Finset.card_pos.mpr ⟨s, hs⟩, Finset.card_pos.mpr ⟨t, ht⟩⟩

private lemma card_erase_add_card_lt {α β : Type*} [DecidableEq α]
    {S : Finset α} {T : Finset β} {s : α} {n : ℕ}
    (hs : s ∈ S) (hn : S.card + T.card = n) : (S.erase s).card + T.card < n := by
  rw [Finset.card_erase_of_mem hs, ← hn]
  suffices 0 < S.card by omega
  exact Finset.card_pos.mpr ⟨s, hs⟩

private lemma card_erase_le_card_erase {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} {s : α} {t : β}
    (hs : s ∈ S) (ht : t ∈ T) (hst : S.card ≤ T.card) :
    (S.erase s).card ≤ (T.erase t).card := by
  rw [Finset.card_erase_of_mem hs, Finset.card_erase_of_mem ht]
  omega

private lemma card_erase_le_card {α β : Type*} [DecidableEq α]
    {S : Finset α} {T : Finset β} {s : α} (hs : s ∈ S) (hst : S.card ≤ T.card) :
    (S.erase s).card ≤ T.card := by
  rw [Finset.card_erase_of_mem hs]
  omega

private lemma card_le_card_erase {α β : Type*} [DecidableEq β]
    {S : Finset α} {T : Finset β} {t : β} (ht : t ∈ T) (hst : S.card < T.card) :
    S.card ≤ (T.erase t).card := by
  rw [Finset.card_erase_of_mem ht]
  omega

private lemma sumsetCardLowerBound_le_card_add :
    ∀ {D d : ℕ} (A B : Finset (Fin D → ℝ)),
      B.Nonempty → B.card ≤ A.card → finsetAffineDim (A + B) = d →
        sumsetCardLowerBound d B.card A.card ≤ (A + B).card := by
  intro D d A B hB hBA hdim
  generalize hn : A.card + B.card = n
  induction n using Nat.strong_induction_on generalizing D d A B
  rename_i n ih
  by_cases hBcard : B.card = 1
  · rw [sumsetCardLowerBound_eq, hBcard]
    simp only [tsub_self, Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero]
    exact Finset.card_le_card_add_right hB
  let hA : A.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hB).trans_le hBA)
  let X := normalize B hB
  let Y := normalize A hA
  rw [← normalize_add_card A B hA hB, ← normalize_card B hB, ← normalize_card A hA]
  rw [add_comm (normalize A hA) (normalize B hB)]
  change sumsetCardLowerBound d X.card Y.card ≤ (X + Y).card
  have h0X : 0 ∈ X := zero_mem_normalize B hB
  have h0Y : 0 ∈ Y := zero_mem_normalize A hA
  have hXtwo : 2 ≤ X.card := by
    simpa [X, normalize_card] using two_le_card_of_nonempty_ne_one B hB hBcard
  have hYtwo : 2 ≤ Y.card := by
    simpa [Y, normalize_card] using
      (two_le_card_of_nonempty_ne_one B hB hBcard).trans hBA
  have hXerase : (X.erase 0).Nonempty := by
    apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
    omega
  have hXYle : X.card ≤ Y.card := by
    simpa [X, Y, normalize_card] using hBA
  have hYXsum : Y.card + X.card = n := by
    simpa [X, Y, normalize_card, add_comm] using hn
  have hcases :
      (finsetAffineDim (X.erase 0 + Y.erase 0) = d ∧
        (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card) ∨
        (finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
          Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card) ∨
        (finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
          Y.card + (X.erase 0 + Y).card ≤ (X + Y).card) ∨
        (finsetAffineDim (X + Y.erase 0) = d - 1 ∧
          X.card + (X + Y.erase 0).card ≤ (X + Y).card) := by
    refine geometric_deletion_cases X Y h0X h0Y ?_ ?_ hXtwo hYtwo ?_
    · intro x hx hx0
      exact normalize_pos_of_ne_zero B hB hx hx0
    · intro y hy hy0
      exact normalize_pos_of_ne_zero A hA hy hy0
    · simpa [X, Y, add_comm] using (normalize_add_dim A B hA hB).trans hdim
  rcases hcases with hfull | hlarge | hsmall | hright
  · apply sumsetCardLowerBound_of_full_case hXtwo
    · have hrec :
          sumsetCardLowerBound d (X.erase 0).card (Y.erase 0).card ≤
            (Y.erase 0 + X.erase 0).card := by
        refine ih ((Y.erase 0).card + (X.erase 0).card) ?_
          (Y.erase 0) (X.erase 0) hXerase ?_ ?_ rfl
        · exact card_erase_add_card_erase_lt h0Y h0X hYXsum
        · exact card_erase_le_card_erase h0X h0Y hXYle
        · simpa [add_comm] using hfull.1
      simpa [X, Y, Finset.card_erase_of_mem h0X,
        Finset.card_erase_of_mem h0Y, add_comm] using hrec
    · exact hfull.2
  · apply sumsetCardLowerBound_of_large_case hXtwo
      hXYle
    · have hrec :
          sumsetCardLowerBound (d - 1) (X.erase 0).card (Y.erase 0).card ≤
            (Y.erase 0 + X.erase 0).card := by
        refine ih ((Y.erase 0).card + (X.erase 0).card) ?_
          (Y.erase 0) (X.erase 0) hXerase ?_ ?_ rfl
        · exact card_erase_add_card_erase_lt h0Y h0X hYXsum
        · exact card_erase_le_card_erase h0X h0Y hXYle
        · simpa [add_comm] using hlarge.1
      simpa [X, Y, Finset.card_erase_of_mem h0X,
        Finset.card_erase_of_mem h0Y, add_comm] using hrec
    · exact hlarge.2
  · apply sumsetCardLowerBound_of_small_case hXtwo
      hXYle
    · have hrec :
          sumsetCardLowerBound (d - 1) (X.erase 0).card Y.card ≤
            (Y + X.erase 0).card := by
        refine ih ((X.erase 0).card + Y.card) ?_
          Y (X.erase 0) hXerase ?_ ?_ ?_
        · apply card_erase_add_card_lt h0X
          simpa [add_comm] using hYXsum
        · exact card_erase_le_card h0X hXYle
        · simpa [add_comm] using hsmall.1
        · omega
      simpa [X, Y, Finset.card_erase_of_mem h0X, add_comm] using hrec
    · exact hsmall.2
  · by_cases hXY : X.card = Y.card
    · rw [hXY]
      apply sumsetCardLowerBound_of_equal_right_case hYtwo
      · have hrec :
            sumsetCardLowerBound (d - 1) (Y.erase 0).card X.card ≤
              (X + Y.erase 0).card := by
          apply ih ((Y.erase 0).card + X.card)
            (card_erase_add_card_lt h0Y hYXsum) X (Y.erase 0)
          · apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
            omega
          · apply card_erase_le_card h0Y
            omega
          · simpa [add_comm] using hright.1
          · omega
        simpa [X, Y, Finset.card_erase_of_mem h0Y, hXY, add_comm] using hrec
      · simpa [hXY] using hright.2
    · have hXYlt : X.card < Y.card := lt_of_le_of_ne hXYle hXY
      refine sumsetCardLowerBound_of_strict_right_case ?_ hXYlt ?_ hright.2
      · omega
      · have hrec :
            sumsetCardLowerBound (d - 1) X.card (Y.erase 0).card ≤
              (Y.erase 0 + X).card := by
          refine ih ((Y.erase 0).card + X.card)
            (card_erase_add_card_lt h0Y hYXsum) (Y.erase 0) X
            (normalize_nonempty B hB) (card_le_card_erase h0Y hXYlt) ?_ rfl
          simpa [add_comm] using hright.1
        simpa [X, Y, Finset.card_erase_of_mem h0Y, add_comm] using hrec

/-- **Ruzsa's theorem.** Let `A, B ⊆ ℝ^D` be finite sets with `B` nonempty and `|B| ≤ |A|`, and
let `d` be the affine dimension of `A + B`. Then
`|A + B| ≥ |A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t)`. -/
theorem card_add_sum_min_le_card_add {D d : ℕ} (A B : Finset (Fin D → ℝ))
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : finsetAffineDim (A + B) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  rw [← sumsetCardLowerBound_eq]
  exact sumsetCardLowerBound_le_card_add A B hB hBA hdim

/-- Ruzsa's theorem for every `d` at most the affine dimension of `A + B`. -/
lemma card_add_sum_min_le_card_add_of_le {D d : ℕ} (A B : Finset (Fin D → ℝ))
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hd : d ≤ finsetAffineDim (A + B)) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) := by
  refine le_trans ?_ (card_add_sum_min_le_card_add A B hB hBA rfl)
  gcongr

end SumOfSetsInSeveralDimensions
