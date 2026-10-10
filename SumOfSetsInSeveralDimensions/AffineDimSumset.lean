/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine dimension of a sumset

The affine dimension of `A + B` is at least the affine dimensions of `A` and of `B` when both
sets are nonempty, and at least the affine dimension of `A ∪ B` minus one.

## Main statements

* `finsetAffineDim_le_finsetAffineDim_add_right`, `finsetAffineDim_le_finsetAffineDim_add_left`:
  the affine dimensions of `A` and `B` are at most that of `A + B`.
* `finsetAffineDim_union_le_sum_add_one`: the affine dimension of `A ∪ B` is at most that of
  `A + B` plus one.
-/

public section

namespace SumOfSetsInSeveralDimensions

open scoped Pointwise Affine

variable {D : ℕ}

/-- The affine dimension of `A` is at most that of `A + B` when `B` is nonempty. -/
lemma finsetAffineDim_le_finsetAffineDim_add_right (A : Finset (Fin D → ℝ))
    {B : Finset (Fin D → ℝ)} (hB : B.Nonempty) : finsetAffineDim A ≤ finsetAffineDim (A + B) := by
  obtain ⟨b, hb⟩ := hB
  rw [← finsetAffineDim_image_add_right b A]
  apply finsetAffineDim_mono
  rw [Finset.image_subset_iff]
  intro a ha
  exact Finset.add_mem_add ha hb

/-- The affine dimension of `B` is at most that of `A + B` when `A` is nonempty. -/
lemma finsetAffineDim_le_finsetAffineDim_add_left {A : Finset (Fin D → ℝ)} (hA : A.Nonempty)
    (B : Finset (Fin D → ℝ)) : finsetAffineDim B ≤ finsetAffineDim (A + B) := by
  rw [add_comm]
  exact finsetAffineDim_le_finsetAffineDim_add_right B hA

/-- The affine span of `A ∪ B` has dimension at most one more than the affine span of `A + B`. -/
lemma finsetAffineDim_union_le_sum_add_one (A B : Finset (Fin D → ℝ))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    finsetAffineDim (A ∪ B) ≤ finsetAffineDim (A + B) + 1 := by
  classical
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  let V := Fin D → ℝ
  let U : Submodule ℝ V := (affineSpan ℝ ((A + B : Finset V) : Set V)).direction
  let L : Submodule ℝ V := Submodule.span ℝ ({b - a} : Set V)
  have hdir :
      (affineSpan ℝ ((A ∪ B : Finset V) : Set V)).direction ≤ U ⊔ L := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
      (s := ((A ∪ B : Finset V) : Set V)) (p := a)]
    · apply Submodule.span_le.mpr
      rintro v ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, Finset.mem_union] at hx
      rcases hx with hxA | hxB
      · apply (le_sup_left : U ≤ U ⊔ L)
        simpa [U, vsub_eq_sub, add_sub_add_right_eq_sub] using
          (affineSpan ℝ ((A + B : Finset V) : Set V)).vsub_mem_direction
            (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add hxA hb))
            (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hb))
      · change (x -ᵥ a : V) ∈ ↑(U ⊔ L)
        convert (U ⊔ L).add_mem (x := x - b) (y := b - a) ?_ ?_ using 1
        · simp only [vsub_eq_sub]
          abel
        · apply (le_sup_left : U ≤ U ⊔ L)
          simpa [U, vsub_eq_sub, add_comm, add_left_comm, add_assoc] using
            (affineSpan ℝ ((A + B : Finset V) : Set V)).vsub_mem_direction
              (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hxB))
              (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hb))
        · apply (le_sup_right : L ≤ U ⊔ L)
          apply Submodule.subset_span
          simp
    · simp [ha]
  apply (Submodule.finrank_mono hdir).trans
  apply (Submodule.finrank_add_le_finrank_add_finrank U L).trans
  apply Nat.add_le_add_left
  simpa [L] using finrank_span_le_card (s := ({b - a} : Set V))

end SumOfSetsInSeveralDimensions
