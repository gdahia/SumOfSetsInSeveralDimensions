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

/-!
# Sum of sets in several dimensions: statements

Ruzsa's lower bound for the cardinality of a sumset in `ℝ^D`, from *Sum of sets in several
dimensions*, Combinatorica 14 (1994), and its closed form, the asymmetric form of Freiman's lemma.
This module imports Mathlib alone; the proofs are supplied by the companion `Solution` module.

The affine dimension of a finite set `S ⊆ ℝ^D` is the dimension of the subspace spanned by the
differences of the points of `S`, written `Module.finrank ℝ (Submodule.span ℝ (S - S))` with the
pointwise difference of sets. This subspace is the direction of the affine span of `S`.

* `card_add_sum_min_le_card_add_of_finrank_span_sub_eq`: Ruzsa's theorem.
* `card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`: the closed form.
-/

public section

open Finset
open scoped Pointwise

namespace SumOfSetsInSeveralDimensions

/-- **Ruzsa's theorem.** Let `A, B ⊆ ℝ^D` be finite sets with `B` nonempty and `|B| ≤ |A|`, and
let `d` be the affine dimension of `A + B`. Then
`|A + B| ≥ |A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t)`. -/
theorem card_add_sum_min_le_card_add_of_finrank_span_sub_eq {D d : ℕ}
    (A B : Finset (Fin D → ℝ)) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ
      (Submodule.span ℝ ((↑(A + B) : Set (Fin D → ℝ)) - (↑(A + B) : Set (Fin D → ℝ)))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  sorry

/-- **The asymmetric form of Freiman's lemma.** Let `A, B ⊆ ℝ^D` be finite sets with `B` nonempty
and `|B| ≤ |A|`, and let `d` be at most the affine dimension of `A + B`. Then
`|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`. -/
theorem card_add_mul_card_le_card_add_add_of_le_finrank_span_sub {D d : ℕ}
    (A B : Finset (Fin D → ℝ)) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ
      (Submodule.span ℝ ((↑(A + B) : Set (Fin D → ℝ)) - (↑(A + B) : Set (Fin D → ℝ))))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  sorry

end SumOfSetsInSeveralDimensions
