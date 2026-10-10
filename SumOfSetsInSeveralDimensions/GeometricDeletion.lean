/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Removing the origin from the summands

Let `X, Y ⊆ ℝ^D` be finite sets with at least two points that contain `0` and whose other
elements are lexicographically positive. Write `X' = X \ {0}` and `Y' = Y \ {0}`, let `d` be the
affine dimension of `X + Y` and let `U` be the direction of the affine span of `X' + Y'`. The
lemma `geometric_deletion_cases` states that one of the following holds.

* `X' + Y'` has dimension `d` and `|X + Y| ≥ |X' + Y'| + d + 1`. The points of `X + Y` outside
  `X' + Y'` are `0` and the points of `(X' ∪ Y') \ (X' + Y')`. Every point of `X + Y` is a sum of
  points of the latter set, by induction along the lexicographic order, so this set has at least
  `d` points.
* `X' + Y'` has dimension `d - 1` and `|X + Y| ≥ |Y| + |X' + Y'|`. Here `X'` has a point outside
  `U`, and `Y` is disjoint from `X' + Y'`.
* `X' + Y` has dimension `d - 1` and `|X + Y| ≥ |Y| + |X' + Y|`. Here `X' + Y'` has dimension
  `d - 2`, and `Y` is disjoint from `X' + Y`.
* `X + Y'` has dimension `d - 1` and `|X + Y| ≥ |X| + |X + Y'|`. Here `X' ⊆ U`, and `X` is disjoint
  from `X + Y'`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open scoped Pointwise

noncomputable section

private lemma right_base_difference_of_eq {D : ℕ} {x y z x₀ y₀ : Fin D → ℝ}
    (hy : y = 0) (hxy : x + y = z) : y₀ = (x - x₀) - (z - y₀) + x₀ := by
  rw [hy, add_zero] at hxy
  rw [← hxy]
  abel

private lemma left_base_difference_of_eq {D : ℕ} {x y z x₀ y₀ : Fin D → ℝ}
    (hxy : x + y = z) : x₀ = (z - y₀) - (y - y₀) - (x - x₀) := by
  rw [← hxy]
  abel

section GeometricDeletion

variable {D d : ℕ}
variable (X Y : Finset (Fin D → ℝ))

private def deletedComplement : Finset (Fin D → ℝ) :=
  ((X.erase 0) ∪ (Y.erase 0)) \ ((X.erase 0) + (Y.erase 0))

private noncomputable def lowerSection (S : Finset (Fin D → ℝ))
    (x : Fin D → ℝ) : Finset (Fin D → ℝ) := by
  classical
  exact S.filter fun y ↦ toLex y < toLex x

private lemma lowerSection_card_lt {S : Finset (Fin D → ℝ)} {x y : Fin D → ℝ}
    (hx : x ∈ S) (hxy : toLex x < toLex y) :
    (lowerSection S x).card < (lowerSection S y).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · rw [lowerSection, Finset.mem_filter]
      exact ⟨hx, hxy⟩
    · rw [lowerSection, Finset.mem_filter]
      intro h
      exact (lt_irrefl (toLex x)) h.2
  · intro z hz
    rw [lowerSection, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩

private lemma add_erase_zero_decomposition (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) :
    X + Y = insert 0 (((X.erase 0) + (Y.erase 0)) ∪
      deletedComplement X Y) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hx0 : x = 0
    · rw [hx0, zero_add]
      by_cases hy0 : y = 0
      · rw [Finset.mem_insert]
        exact Or.inl hy0
      · rw [Finset.mem_insert]
        right
        by_cases hyP : y ∈ X.erase 0 + Y.erase 0
        · exact Finset.mem_union_left _ hyP
        · apply Finset.mem_union_right
          rw [deletedComplement, Finset.mem_sdiff]
          exact ⟨Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hy0, hy⟩), hyP⟩
    · by_cases hy0 : y = 0
      · rw [hy0, add_zero, Finset.mem_insert]
        right
        by_cases hxP : x ∈ X.erase 0 + Y.erase 0
        · exact Finset.mem_union_left _ hxP
        · apply Finset.mem_union_right
          rw [deletedComplement, Finset.mem_sdiff]
          exact ⟨Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hx0, hx⟩), hxP⟩
      · rw [Finset.mem_insert]
        right
        apply Finset.mem_union_left
        exact Finset.add_mem_add (Finset.mem_erase.2 ⟨hx0, hx⟩)
          (Finset.mem_erase.2 ⟨hy0, hy⟩)
  · intro hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa using Finset.add_mem_add h0X h0Y
    · rw [Finset.mem_union] at hz
      rcases hz with hz | hz
      · rw [Finset.mem_add] at hz ⊢
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩
      · rw [deletedComplement, Finset.mem_sdiff, Finset.mem_union] at hz
        rcases hz.1 with hz | hz
        · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hz) h0Y
        · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hz)

private lemma zero_notMem_add_erase_zero
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) :
    0 ∉ X.erase 0 + Y.erase 0 := by
  intro hzero
  rw [Finset.mem_add] at hzero
  obtain ⟨x, hx, y, hy, hxy⟩ := hzero
  refine (add_pos (b := 0) (c := toLex x) (a := toLex y) ?_ ?_).ne' ?_
  · exact hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
  · exact hposY y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
  · rw [← toLex_add, hxy, toLex_zero]

private lemma span_deleted_complement
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) :
    ∀ z ∈ X + Y,
      z ∈ Submodule.span ℝ (deletedComplement X Y : Set (Fin D → ℝ)) := by
  classical
  intro z hz
  generalize hk : (lowerSection (X + Y) z).card = k
  induction k using Nat.strong_induction_on generalizing z
  rename_i k ih
  by_cases hz0 : z = 0
  · rw [hz0]
    exact Submodule.zero_mem _
  by_cases hzC : z ∈ deletedComplement X Y
  · exact Submodule.subset_span hzC
  rw [add_erase_zero_decomposition X Y h0X h0Y, Finset.mem_insert,
    Finset.mem_union] at hz
  rcases hz with hz | hz | hz
  · exact (hz0 hz).elim
  · rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · apply ih (lowerSection (X + Y) x).card
      · rw [← hk]
        apply lowerSection_card_lt
        · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hx) h0Y
        · rw [toLex_add]
          exact lt_add_of_pos_right _
            (hposY y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
      · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hx) h0Y
      · rfl
    · apply ih (lowerSection (X + Y) y).card
      · rw [← hk]
        apply lowerSection_card_lt
        · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hy)
        · rw [toLex_add]
          exact lt_add_of_pos_left _
            (hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
      · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hy)
      · rfl
  · exact (hzC hz).elim

private lemma finsetAffineDim_le_card_of_span {S C : Finset (Fin D → ℝ)}
    (h0 : 0 ∈ S) (hspan : ∀ x ∈ S, x ∈ Submodule.span ℝ (C : Set (Fin D → ℝ))) :
    finsetAffineDim S ≤ C.card := by
  unfold finsetAffineDim
  rw [direction_affineSpan]
  refine (Submodule.finrank_mono ?_).trans (finrank_span_finset_le_card C)
  · rw [vectorSpan_eq_span_vsub_set_right ℝ (s := (S : Set (Fin D → ℝ))) (p := 0) h0]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    simpa using hspan x hx

private lemma finsetAffineDim_le_finrank_of_mem {S : Finset (Fin D → ℝ)}
    (U : Submodule ℝ (Fin D → ℝ)) (h0 : 0 ∈ S) (hmem : ∀ x ∈ S, x ∈ U) :
    finsetAffineDim S ≤ Module.finrank ℝ U := by
  unfold finsetAffineDim
  rw [direction_affineSpan]
  apply Submodule.finrank_mono
  rw [vectorSpan_eq_span_vsub_set_right ℝ (s := (S : Set (Fin D → ℝ))) (p := 0) h0]
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  simpa using hmem x hx

private lemma left_vsub_mem_deleted_direction
    {x₀ y₀ x : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hx : x ∈ X.erase 0) :
    x - x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx hy₀))
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma right_vsub_mem_deleted_direction
    {x₀ y₀ y : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hy : y ∈ Y.erase 0) :
    y - y₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy))
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma sum_vsub_mem_deleted_direction
    {x₀ y₀ z : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hz : z ∈ X.erase 0 + Y.erase 0) :
    z - (x₀ + y₀) ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ hz)
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma finrank_deleted_direction_eq {e : ℕ}
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) :
    Module.finrank ℝ
      (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
        Set (Fin D → ℝ))).direction = e := by
  simpa [finsetAffineDim] using hdel

private lemma add_mem_direction_sup_span_pair
    {x₀ y₀ : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (z : Fin D → ℝ) (hz : z ∈ X + Y) :
    z ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀, y₀} : Set (Fin D → ℝ)) := by
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  apply Submodule.add_mem
  · by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    · rw [← sub_add_cancel x x₀]
      apply Submodule.add_mem_sup
      · apply left_vsub_mem_deleted_direction X Y hx₀ hy₀
        exact Finset.mem_erase.2 ⟨hx0, hx⟩
      · apply Submodule.subset_span
        simp
  · by_cases hy0 : y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    · rw [← sub_add_cancel y y₀]
      apply Submodule.add_mem_sup
      · apply right_vsub_mem_deleted_direction X Y hx₀ hy₀
        exact Finset.mem_erase.2 ⟨hy0, hy⟩
      · apply Submodule.subset_span
        simp

private lemma deleted_dim_add_two_ge
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0) :
    finsetAffineDim (X + Y) ≤ finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  refine le_trans (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀, y₀} : Set (Fin D → ℝ)))
    ?_ ?_) ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    exact add_mem_direction_sup_span_pair X Y hx₀ hy₀ z hz
  · refine le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) ?_
    apply Nat.add_le_add
    · rfl
    · rw [← Finset.coe_pair]
      simpa [Set.finrank] using
        (finrank_span_finset_le_card (R := ℝ)
          ({x₀, y₀} : Finset (Fin D → ℝ))).trans (Finset.card_le_two)

private lemma finsetAffineDim_le_finrank_of_vsub {S : Finset (Fin D → ℝ)}
    (U : Submodule ℝ (Fin D → ℝ)) {p : Fin D → ℝ} (hp : p ∈ S)
    (hmem : ∀ x ∈ S, x - p ∈ U) : finsetAffineDim S ≤ Module.finrank ℝ U := by
  unfold finsetAffineDim
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
    (s := (S : Set (Fin D → ℝ))) (p := p) hp]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  simpa [vsub_eq_sub] using hmem x hx

private lemma add_eq_union_add_erase_right (h0Y : 0 ∈ Y) :
    X + Y = X ∪ (X + Y.erase 0) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hy0 : y = 0
    · rw [hy0, add_zero]
      exact Finset.mem_union_left _ hx
    · apply Finset.mem_union_right
      exact Finset.add_mem_add hx (Finset.mem_erase.2 ⟨hy0, hy⟩)
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add hz h0Y
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, rfl⟩

private lemma add_eq_union_erase_left_add (h0X : 0 ∈ X) :
    X + Y = Y ∪ (X.erase 0 + Y) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hx0 : x = 0
    · rw [hx0, zero_add]
      exact Finset.mem_union_left _ hy
    · apply Finset.mem_union_right
      exact Finset.add_mem_add (Finset.mem_erase.2 ⟨hx0, hx⟩) hy
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add h0X hz
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, hy, rfl⟩

private lemma deleted_dim_eq_pred_of_left_base_mem
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) : e = d - 1 := by
  suffices d ≤ e + 1 by omega
  rw [← hdim]
  refine (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
    ?_ ?_).trans ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · refine (le_sup_left :
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ≤
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ))) ?_
        rw [← sub_add_cancel x x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        apply Submodule.add_mem_sup
        · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hy0, hy⟩)
        · apply Submodule.subset_span
          simp
  · apply le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
    rw [finrank_deleted_direction_eq X Y hdel]
    apply Nat.add_le_add_left
    rw [← Finset.coe_singleton]
    simpa [Set.finrank] using
      (finrank_span_finset_le_card (R := ℝ) ({y₀} : Finset (Fin D → ℝ))).trans_eq
        (Finset.card_singleton y₀)

private lemma right_base_not_mem_of_left_base_mem
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    y₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  intro hyU
  apply Nat.not_le_of_lt hed
  rw [← hdel, ← hdim]
  apply finsetAffineDim_le_finrank_of_mem
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel x x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        exact Submodule.add_mem _
          (right_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hy0, hy⟩)) hyU

private lemma left_base_mem_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X + Y.erase 0) = d - 1 ∧
      X.card + (X + Y.erase 0).card ≤ (X + Y).card := by
  rw [← deleted_dim_eq_pred_of_left_base_mem X Y h0X h0Y hx₀ hy₀ hdim hdel hed hxU]
  constructor
  · apply Nat.le_antisymm
    · refine (finsetAffineDim_le_finrank_of_vsub
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction
        (p := y₀) ?_ ?_).trans ?_
      · simpa using Finset.add_mem_add h0X hy₀
      · intro z hz
        rw [Finset.mem_add] at hz
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [sub_eq_add_neg, add_assoc]
        apply Submodule.add_mem
        · by_cases hx0 : x = 0
          · rw [hx0]
            exact Submodule.zero_mem _
          · rw [← sub_add_cancel x x₀]
            exact Submodule.add_mem _
              (left_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
        · simpa [sub_eq_add_neg] using right_vsub_mem_deleted_direction X Y hx₀ hy₀ hy
      · simpa [finsetAffineDim] using hdel.le
    · rw [← hdel]
      apply finsetAffineDim_mono
      intro z hz
      rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, hy, rfl⟩
  · rw [add_eq_union_add_erase_right X Y h0Y, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro z hzX hzT
    apply right_base_not_mem_of_left_base_mem X Y h0X h0Y hx₀ hy₀ hdim hdel hed hxU
    convert
      (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
        Set (Fin D → ℝ))).direction.sub_mem (x := z) (y := z - y₀) ?_ ?_ using 1
    · abel
    · by_cases hz0 : z = 0
      · rw [hz0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel z x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hz0, hzX⟩)) hxU
    · rw [Finset.mem_add] at hzT
      obtain ⟨x, hx, y, hy, rfl⟩ := hzT
      rw [sub_eq_add_neg, add_assoc]
      apply Submodule.add_mem
      · by_cases hx0 : x = 0
        · rw [hx0]
          exact Submodule.zero_mem _
        · rw [← sub_add_cancel x x₀]
          exact Submodule.add_mem _
            (left_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
      · simpa [sub_eq_add_neg] using right_vsub_mem_deleted_direction X Y hx₀ hy₀ hy

private lemma left_base_not_mem_codimension_one_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (_h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (he : e = d - 1)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
      Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card := by
  constructor
  · exact hdel.trans he
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add h0X hz
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩
  · rw [Finset.disjoint_left]
    intro z hzY hzP
    by_cases hz0 : z = 0
    · subst z
      exact zero_notMem_add_erase_zero X Y hposX hposY hzP
    · apply hxU
      convert
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction.sub_mem
            (x := z - y₀) (y := z - (x₀ + y₀)) ?_ ?_ using 1
      · abel
      · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
          (Finset.mem_erase.2 ⟨hz0, hzY⟩)
      · exact sum_vsub_mem_deleted_direction X Y hx₀ hy₀ hzP

private lemma right_base_not_mem_direction_sup_left
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (_hed : e < d)
    (he : d = e + 2)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    y₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)) := by
  intro hyW
  suffices d ≤ e + 1 by omega
  rw [← hdim]
  refine (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
    ?_ ?_).trans ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel x x₀]
        apply Submodule.add_mem_sup
        · exact left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)
        · apply Submodule.subset_span
          simp
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        exact Submodule.add_mem _
          ((le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hy0, hy⟩))) hyW
  · rw [Submodule.finrank_sup_span_singleton hxU]
    simpa [finsetAffineDim] using Nat.add_le_add_right hdel.le 1

private lemma codimension_two_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (he : d = e + 2)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
      Y.card + (X.erase 0 + Y).card ≤ (X + Y).card := by
  simp only [he, Nat.add_one_sub_one]
  constructor
  · apply Nat.le_antisymm
    · refine (finsetAffineDim_le_finrank_of_vsub
        ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
        (p := x₀) ?_ ?_).trans ?_
      · simpa using Finset.add_mem_add hx₀ h0Y
      · intro z hz
        rw [Finset.mem_add] at hz
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [sub_eq_add_neg, add_assoc, add_comm y (-x₀), ← add_assoc]
        apply Submodule.add_mem
        · exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
            (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)
        · by_cases hy0 : y = 0
          · rw [hy0]
            exact Submodule.zero_mem _
          · rw [← sub_add_cancel y y₀]
            apply Submodule.add_mem_sup
            · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hy0, hy⟩)
            · apply Submodule.subset_span
              simp
      · rw [Submodule.finrank_sup_span_singleton]
        · simpa [finsetAffineDim] using Nat.add_le_add_right hdel.le 1
        · intro hyU
          apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
          exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ))) hyU
    · rw [← finrank_deleted_direction_eq X Y hdel]
      rw [← Submodule.finrank_sup_span_singleton]
      · apply Submodule.finrank_mono
        apply sup_le
        · apply AffineSubspace.direction_le
          apply affineSpan_mono
          intro z hz
          change z ∈ X.erase 0 + Y.erase 0 at hz
          change z ∈ X.erase 0 + Y
          rw [Finset.mem_add] at hz ⊢
          obtain ⟨x, hx, y, hy, rfl⟩ := hz
          exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, rfl⟩
        · apply Submodule.span_le.mpr
          · intro z hz
            rw [Set.mem_singleton_iff] at hz
            · subst z
              simpa [vsub_eq_sub] using
                (affineSpan ℝ ((X.erase 0 + Y : Finset (Fin D → ℝ)) :
                  Set (Fin D → ℝ))).vsub_mem_direction
                    (subset_affineSpan ℝ _
                      (Finset.add_mem_add hx₀ (Finset.mem_of_mem_erase hy₀)))
                    (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ h0Y))
      · intro hyU
        apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
        exact (le_sup_left :
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ≤
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ))) hyU
  · rw [add_eq_union_erase_left_add X Y h0X, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro z hzY hzT
    rw [Finset.mem_add] at hzT
    obtain ⟨x, hx, y, hy, hxy⟩ := hzT
    by_cases hz0 : z = 0
    · subst z
      by_cases hy0 : y = 0
      · apply Finset.ne_of_mem_erase hx
        rw [hy0, add_zero] at hz0
        exact hz0
      · refine (add_pos (b := 0) (c := toLex x) (a := toLex y) ?_ ?_).ne' ?_
        · exact hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
        · exact hposY y hy hy0
        · rw [← toLex_add, hz0, toLex_zero]
    · by_cases hy0 : y = 0
      · apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
        rw [right_base_difference_of_eq (x₀ := x₀) (y₀ := y₀) hy0 hxy]
        apply Submodule.add_mem
        · exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (Submodule.sub_mem _
              (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)
              (right_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hz0, hzY⟩)))
        · exact (le_sup_right : Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)) ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (Submodule.mem_span_singleton_self x₀)
      · apply hxU
        rw [left_base_difference_of_eq (x₀ := x₀) (y₀ := y₀) hxy]
        exact Submodule.sub_mem _
          (Submodule.sub_mem _
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hz0, hzY⟩))
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hy0, hy⟩)))
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)

private lemma full_dim_deletion_card
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdim : finsetAffineDim (X + Y) = d) :
    (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card := by
  classical
  rw [add_erase_zero_decomposition X Y h0X h0Y, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint]
    · apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      rw [← hdim]
      apply finsetAffineDim_le_card_of_span
      · simpa using Finset.add_mem_add h0X h0Y
      · exact span_deleted_complement X Y h0X h0Y hposX hposY
    · exact Finset.disjoint_sdiff
  · rw [Finset.mem_union]
    push Not
    constructor
    · exact zero_notMem_add_erase_zero X Y hposX hposY
    intro hzero
    rw [deletedComplement, Finset.mem_sdiff] at hzero
    simpa using hzero.1

private lemma deleted_dim_lt_of_ne
    (hdim : finsetAffineDim (X + Y) = d)
    (hne : finsetAffineDim (X.erase 0 + Y.erase 0) ≠ d) :
    finsetAffineDim (X.erase 0 + Y.erase 0) < d := by
  refine Nat.lt_of_le_of_ne ?_ hne
  · rw [← hdim]
    apply finsetAffineDim_mono
    intro z hz
    rw [Finset.mem_add] at hz ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩

private lemma deleted_dim_le_add_two
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d) :
    d ≤ finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  rw [← hdim]
  exact deleted_dim_add_two_ge X Y h0X h0Y hx₀ hy₀

private lemma deleted_dim_gap_cases
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hne : finsetAffineDim (X.erase 0 + Y.erase 0) ≠ d) :
    d = finsetAffineDim (X.erase 0 + Y.erase 0) + 1 ∨
      d = finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  rcases Nat.eq_or_lt_of_le (deleted_dim_le_add_two X Y h0X h0Y hx₀ hy₀ hdim) with heq | hlt
  · right
    exact heq
  · left
    rcases Nat.exists_eq_add_of_lt (deleted_dim_lt_of_ne X Y hdim hne) with ⟨k, rfl⟩
    omega

/-- Let `X` and `Y` contain `0`, have at least two points each, and have all other elements
lexicographically positive, and let `X + Y` have affine dimension `d`. Then removing `0` from `X`,
from `Y` or from both gives a sumset of dimension `d` with at least `d + 1` fewer points, or a
sumset of dimension `d - 1` with at least `|Y|` or `|X|` fewer points, as listed in the
statement. -/
lemma geometric_deletion_cases
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hXcard : 2 ≤ X.card) (hYcard : 2 ≤ Y.card)
    (hdim : finsetAffineDim (X + Y) = d) :
    (finsetAffineDim (X.erase 0 + Y.erase 0) = d ∧
      (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card) ∨
      (finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
        Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card) ∨
      (finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
        Y.card + (X.erase 0 + Y).card ≤ (X + Y).card) ∨
      (finsetAffineDim (X + Y.erase 0) = d - 1 ∧
        X.card + (X + Y.erase 0).card ≤ (X + Y).card) := by
  classical
  by_cases hdimdel : finsetAffineDim (X.erase 0 + Y.erase 0) = d
  · left
    exact ⟨hdimdel, full_dim_deletion_card X Y h0X h0Y hposX hposY hdim⟩
  · right
    obtain ⟨x₀, hx₀⟩ : (X.erase 0).Nonempty := by
      apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
      omega
    obtain ⟨y₀, hy₀⟩ : (Y.erase 0).Nonempty := by
      apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
      omega
    by_cases hxU : x₀ ∈
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction
    · right
      right
      exact left_base_mem_deletion X Y h0X h0Y hx₀ hy₀ hdim rfl
        (deleted_dim_lt_of_ne X Y hdim hdimdel) hxU
    · rcases deleted_dim_gap_cases X Y h0X h0Y hx₀ hy₀ hdim hdimdel with hcodim | hcodim
      · left
        refine left_base_not_mem_codimension_one_deletion X Y h0X h0Y hx₀ hy₀
          hposX hposY rfl ?_ hxU
        omega
      · right
        left
        apply codimension_two_deletion X Y h0X h0Y hx₀ hy₀ hposX hposY hdim rfl
          (deleted_dim_lt_of_ne X Y hdim hdimdel) hcodim hxU

end GeometricDeletion

end

end SumOfSetsInSeveralDimensions
