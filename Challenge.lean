/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat

/-!
# Sum of sets in several dimensions

Theorems 1 and 2 and Corollary 1.1 of Ruzsa, *Sum of sets in several dimensions*, Combinatorica 14
(1994): a lower bound for the size of a sumset in `ℝ^D`, the fact that it is the least size of
such a sumset, and its closed form, the asymmetric form of Freiman's lemma. The affine dimension of
a finite set `S ⊆ ℝ^D` is the dimension of the span of `S - S`. The proofs are in `Solution.lean`.
-/

public section

open Finset
open scoped Pointwise

namespace SumOfSetsInSeveralDimensions

/-- **Ruzsa's theorem.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty, `|B| ≤ |A|` and `A + B` has
affine dimension `d`, then `|A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_card_add_of_finrank_span_sub_eq' {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  sorry

/-- **The asymmetric form of Freiman's lemma.** If `A, B ⊆ ℝ^D` are finite, `B` is nonempty,
`|B| ≤ |A|` and `A + B` has affine dimension at least `d`, then
`|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`. -/
theorem card_add_mul_card_le_card_add_add_of_le_finrank_span_sub' {D d : ℕ}
    {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin D → ℝ)))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  sorry

/-- **Ruzsa's Theorem 2.** For `d ≥ 1`, `1 ≤ m ≤ n` and `n ≥ d + 1`, the least size of `A + B`
over `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `A + B` of affine dimension `d` is
`n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`. -/
theorem sInf_card_add_eq_add_sum_min' {d m n : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin d → ℝ))) = d ∧
      #(A + B) = k} = n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) :=
  sorry

/-- **Ruzsa's Theorem 2, with `B` of full dimension.** For `d ≥ 1`, `1 ≤ m ≤ n` and `n ≥ d + 1`,
the least size of `A + B` over `A, B ⊆ ℝ^d` with `|A| = m`, `|B| = n` and `B` of affine dimension
`d` is `n + ∑ j ∈ {1, …, m - 1}, min d (n - j)`. -/
theorem sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min' {d m n : ℕ} (hd : 1 ≤ d)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑B - ↑B : Set (Fin d → ℝ))) = d ∧ #(A + B) = k} =
      n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) :=
  sorry

end SumOfSetsInSeveralDimensions
