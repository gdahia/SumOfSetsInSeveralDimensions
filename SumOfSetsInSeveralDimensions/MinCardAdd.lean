/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.AffineDim
public import SumOfSetsInSeveralDimensions.LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import SumOfSetsInSeveralDimensions.AffineDimSumset
import SumOfSetsInSeveralDimensions.Construction
import SumOfSetsInSeveralDimensions.LowerBound

/-!
# The least size of a sumset in `ℝ^d`

Ruzsa's paper defines `F_d(m, n)` as the least `|A + B|` over sets `A, B ⊆ ℝ^d` with `|A| = m`,
`|B| = n` and `A + B` of affine dimension `d`, and `F'_d(m, n)` as the same minimum with `B` of
affine dimension `d` instead. Theorem 2 of the paper states that `F_d(m, n) = F'_d(m, n) =
G_d(m, n)` for `1 ≤ m ≤ n`, unless `n < d + 1` or `m ≤ n - m ≤ d`. The sets of Section 3 attain
`G_d(m, n)` for all `1 ≤ m ≤ n` with `d + 1 ≤ n`, so the equalities hold for these pairs, which
include those excluded by the second condition.

## Main definitions

* `minCardAdd d m n`: the function `F_d(m, n)`.
* `minCardAddOfDimRight d m n`: the function `F'_d(m, n)`.

## Main statements

* `minCardAdd_eq_sumsetCardLowerBound`, `minCardAddOfDimRight_eq_sumsetCardLowerBound`: Theorem 2.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

/-- `F_d(m, n)`: the least size of `A + B` for `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `A + B`
of affine dimension `d`. -/
noncomputable def minCardAdd (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ finsetAffineDim (A + B) = d ∧
    #(A + B) = k}

/-- `F'_d(m, n)`: the least size of `A + B` for `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `B`
of affine dimension `d`. -/
noncomputable def minCardAddOfDimRight (d m n : ℕ) : ℕ :=
  sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧ finsetAffineDim B = d ∧ #(A + B) = k}

variable {d m n : ℕ}

private lemma sumsetCardLowerBound_le_card_add {A B : Finset (Fin d → ℝ)} (hm : 1 ≤ m)
    (hmn : m ≤ n) (hA : #A = m) (hB : #B = n) (hdim : finsetAffineDim (A + B) = d) :
    sumsetCardLowerBound d m n ≤ #(A + B) := by
  have h := card_add_sum_min_le_card_add (d := d) (A := B) (B := A) (card_pos.1 (by grind))
    (by grind) (by rwa [add_comm])
  rwa [add_comm B, hA, hB, ← sumsetCardLowerBound_eq] at h

/-- **Theorem 2 of Ruzsa, for `F_d`.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`,
`F_d(m, n) = G_d(m, n)`. -/
theorem minCardAdd_eq_sumsetCardLowerBound (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAdd d m n = sumsetCardLowerBound d m n := by
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_eq_sumsetCardLowerBound hd hm hmn hn
  have hdim : finsetAffineDim (A + B) = d := by
    rw [add_comm]
    exact finsetAffineDim_add_eq_of_left_eq (card_pos.1 (by grind)) hBdim
  refine le_antisymm (Nat.sInf_le ⟨A, B, hA, hB, hdim, hAB⟩)
    (le_csInf ⟨_, A, B, hA, hB, hdim, rfl⟩ ?_)
  rintro k ⟨A', B', hA', hB', hdim', rfl⟩
  exact sumsetCardLowerBound_le_card_add hm hmn hA' hB' hdim'

/-- **Theorem 2 of Ruzsa, for `F'_d`.** For `1 ≤ d`, `1 ≤ m ≤ n` and `d + 1 ≤ n`,
`F'_d(m, n) = G_d(m, n)`. -/
theorem minCardAddOfDimRight_eq_sumsetCardLowerBound (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAddOfDimRight d m n = sumsetCardLowerBound d m n := by
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_eq_sumsetCardLowerBound hd hm hmn hn
  refine le_antisymm (Nat.sInf_le ⟨A, B, hA, hB, hBdim, hAB⟩)
    (le_csInf ⟨_, A, B, hA, hB, hBdim, rfl⟩ ?_)
  rintro k ⟨A', B', hA', hB', hBdim', rfl⟩
  refine sumsetCardLowerBound_le_card_add hm hmn hA' hB' ?_
  rw [add_comm]
  exact finsetAffineDim_add_eq_of_left_eq (card_pos.1 (by grind)) hBdim'

end SumOfSetsInSeveralDimensions
