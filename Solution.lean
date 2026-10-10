/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.ClosedForm
public import SumOfSetsInSeveralDimensions.LowerBound

/-!
# Sum of sets in several dimensions: proofs

Proofs of the statements of `Challenge.lean`. They follow from `card_add_sum_min_le_card_add` and
`card_add_mul_card_le_card_add_add`, which are stated with `finsetAffineDim`, and from
`finsetAffineDim_eq_finrank_vectorSpan`.
-/

public section

open Finset
open scoped Pointwise

namespace SumOfSetsInSeveralDimensions

private lemma finsetAffineDim_eq_finrank_span_sub {D : ℕ} (S : Finset (Fin D → ℝ)) :
    finsetAffineDim S = Module.finrank ℝ
      (Submodule.span ℝ ((S : Set (Fin D → ℝ)) - (S : Set (Fin D → ℝ)))) := by
  rw [finsetAffineDim_eq_finrank_vectorSpan, vectorSpan_def]
  rfl

/-- **Ruzsa's theorem.** Let `A, B ⊆ ℝ^D` be finite sets with `B` nonempty and `|B| ≤ |A|`, and
let `d` be the affine dimension of `A + B`. Then
`|A + B| ≥ |A| + ∑ t ∈ {1, …, |B| - 1}, min d (|A| - t)`. -/
theorem card_add_sum_min_le_card_add_of_finrank_span_sub_eq {D d : ℕ}
    (A B : Finset (Fin D → ℝ)) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : Module.finrank ℝ
      (Submodule.span ℝ ((↑(A + B) : Set (Fin D → ℝ)) - (↑(A + B) : Set (Fin D → ℝ)))) = d) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min d (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add A B hB hBA ((finsetAffineDim_eq_finrank_span_sub _).trans hdim)

/-- **The asymmetric form of Freiman's lemma.** Let `A, B ⊆ ℝ^D` be finite sets with `B` nonempty
and `|B| ≤ |A|`, and let `d` be at most the affine dimension of `A + B`. Then
`|A| + d * |B| ≤ |A + B| + d * (d + 1) / 2`. -/
theorem card_add_mul_card_le_card_add_add_of_le_finrank_span_sub {D d : ℕ}
    (A B : Finset (Fin D → ℝ)) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hd : d ≤ Module.finrank ℝ
      (Submodule.span ℝ ((↑(A + B) : Set (Fin D → ℝ)) - (↑(A + B) : Set (Fin D → ℝ))))) :
    #A + d * #B ≤ #(A + B) + d * (d + 1) / 2 :=
  card_add_mul_card_le_card_add_add A B hB hBA
    (hd.trans_eq (finsetAffineDim_eq_finrank_span_sub _).symm)

end SumOfSetsInSeveralDimensions
