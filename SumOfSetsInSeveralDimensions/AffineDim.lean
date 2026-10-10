/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine dimension of a finite set

The affine dimension of a finite set `S ⊆ ℝ^D` is the dimension of the direction of its affine
span. The direction of the affine span of `S` is the vector span of `S`, the subspace spanned by
the differences of the points of `S`.

## Main definitions

* `finsetAffineDim S`: the affine dimension of `S`.

## Main statements

* `finsetAffineDim_eq_finrank_vectorSpan`: `finsetAffineDim S` is the dimension of
  `vectorSpan ℝ S`.
* `finsetAffineDim_mono`: the affine dimension is monotone.
* `finsetAffineDim_vadd_finset`, `finsetAffineDim_image_add_left`,
  `finsetAffineDim_image_add_right`, `finsetAffineDim_image_sub`: it is invariant under
  translation.
* `finsetAffineDim_add_one_le_card`: a nonempty set of affine dimension `d` has at least `d + 1`
  points.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open scoped Pointwise

variable {D : ℕ}

/-- The affine dimension of a finite set `S ⊆ ℝ^D`: the dimension of the direction of the affine
span of `S`. -/
noncomputable def finsetAffineDim (S : Finset (Fin D → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (S : Set (Fin D → ℝ))).direction

/-- The affine dimension of `S` is the dimension of the vector span of `S`. -/
lemma finsetAffineDim_eq_finrank_vectorSpan (S : Finset (Fin D → ℝ)) :
    finsetAffineDim S = Module.finrank ℝ (vectorSpan ℝ (S : Set (Fin D → ℝ))) := by
  rw [finsetAffineDim, direction_affineSpan]

/-- Affine dimension is monotone under inclusion of finite sets. -/
lemma finsetAffineDim_mono {S T : Finset (Fin D → ℝ)}
    (hST : S ⊆ T) : finsetAffineDim S ≤ finsetAffineDim T := by
  unfold finsetAffineDim
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  simpa using hST

/-- The affine dimension of a subset of `ℝ^D` is at most `D`. -/
lemma finsetAffineDim_le (S : Finset (Fin D → ℝ)) : finsetAffineDim S ≤ D :=
  (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun ℝ)

@[simp]
lemma finsetAffineDim_empty : finsetAffineDim (∅ : Finset (Fin D → ℝ)) = 0 := by
  simp [finsetAffineDim_eq_finrank_vectorSpan]

@[simp]
lemma finsetAffineDim_singleton (x : Fin D → ℝ) : finsetAffineDim {x} = 0 := by
  simp [finsetAffineDim_eq_finrank_vectorSpan]

/-- The affine dimension is invariant under translation. -/
@[simp]
lemma finsetAffineDim_vadd_finset (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    finsetAffineDim (c +ᵥ S) = finsetAffineDim S := by
  rw [finsetAffineDim_eq_finrank_vectorSpan, Finset.coe_vadd_finset, vectorSpan_vadd,
    finsetAffineDim_eq_finrank_vectorSpan]

/-- The affine dimension of `c + S` is that of `S`. -/
lemma finsetAffineDim_image_add_left (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    finsetAffineDim (S.image (c + ·)) = finsetAffineDim S :=
  finsetAffineDim_vadd_finset c S

/-- The affine dimension of `S + c` is that of `S`. -/
lemma finsetAffineDim_image_add_right (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    finsetAffineDim (S.image (· + c)) = finsetAffineDim S := by
  simp only [add_comm _ c, finsetAffineDim_image_add_left]

/-- The affine dimension of `S - c` is that of `S`. -/
lemma finsetAffineDim_image_sub (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    finsetAffineDim (S.image fun x ↦ x - c) = finsetAffineDim S := by
  simp only [sub_eq_add_neg, finsetAffineDim_image_add_right]

/-- A nonempty finite set of affine dimension `d` contains at least `d + 1` points. -/
lemma finsetAffineDim_add_one_le_card (S : Finset (Fin D → ℝ))
    (hS : S.Nonempty) : finsetAffineDim S + 1 ≤ S.card := by
  classical
  let : Nonempty S := hS.to_subtype
  let p : S → (Fin D → ℝ) := Subtype.val
  have hp : Set.range p = (S : Set (Fin D → ℝ)) := by
    ext x
    simp [p]
  unfold finsetAffineDim
  rw [direction_affineSpan, ← hp]
  simpa only [Fintype.card_coe] using finrank_vectorSpan_range_add_one_le ℝ p

/-- The affine dimension of a finite set is at most its number of points. -/
lemma finsetAffineDim_le_card (S : Finset (Fin D → ℝ)) :
    finsetAffineDim S ≤ S.card := by
  by_cases hS : S.Nonempty
  · exact (Nat.le_add_right _ _).trans (finsetAffineDim_add_one_le_card S hS)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, finsetAffineDim]

end SumOfSetsInSeveralDimensions
