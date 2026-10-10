/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Tactic.Abel

/-!
# Translating a set so that its lexicographic minimum is the origin

Order `ℝ^D` lexicographically. The translate `normalize S` of a nonempty finite set `S` by minus
its least element contains `0`, and its other elements are positive. Cardinalities of sets and
sumsets and the affine dimension of a sumset do not change under this translation.
-/

public section

namespace SumOfSetsInSeveralDimensions

open scoped Pointwise

section LexicographicMinimum

variable {D : ℕ}

private noncomputable def lexMin (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Fin D → ℝ :=
  by
    refine ofLex ((S.image toLex).min' ?_)
    simpa

private lemma lexMin_mem (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : lexMin S hS ∈ S := by
  rw [lexMin]
  obtain ⟨x, hx, hxmin⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image toLex) _)
  rw [← hxmin, ofLex_toLex]
  exact hx

private lemma lexMin_le (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) {x : Fin D → ℝ}
    (hx : x ∈ S) : toLex (lexMin S hS) ≤ toLex x := by
  rw [lexMin, toLex_ofLex]
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨x, hx, rfl⟩

private lemma lexMin_sub_pos (S : Finset (Fin D → ℝ)) (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ S) (hne : x ≠ lexMin S hS) :
    0 < toLex (x - lexMin S hS) := by
  rw [toLex_sub, sub_pos]
  apply (lexMin_le S hS hx).lt_of_ne
  simpa using hne.symm

end LexicographicMinimum

section Normalize

variable {D : ℕ}

/-- The translate of a nonempty finite set `S ⊆ ℝ^D` by minus its lexicographically least
element. -/
noncomputable def normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Finset (Fin D → ℝ) :=
  S.image fun x ↦ x - lexMin S hS

/-- Translation does not change the number of points. -/
lemma normalize_card (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    (normalize S hS).card = S.card := by
  rw [normalize, Finset.card_image_of_injective]
  intro x y hxy
  exact sub_left_injective hxy

/-- The translated set contains the origin. -/
lemma zero_mem_normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    0 ∈ normalize S hS := by
  rw [normalize, Finset.mem_image]
  exact ⟨lexMin S hS, lexMin_mem S hS, sub_self _⟩

/-- The translated set is nonempty. -/
lemma normalize_nonempty (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    (normalize S hS).Nonempty := ⟨0, zero_mem_normalize S hS⟩

/-- The nonzero elements of the translated set are lexicographically positive. -/
lemma normalize_pos_of_ne_zero (S : Finset (Fin D → ℝ)) (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ normalize S hS) (hx0 : x ≠ 0) : 0 < toLex x := by
  rw [normalize, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply lexMin_sub_pos S hS hy
  intro hymin
  apply hx0
  rw [hymin, sub_self]

private lemma normalize_add (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty) (hB : B.Nonempty) :
    normalize A hA + normalize B hB =
      (A + B).image fun x ↦ x - (lexMin A hA + lexMin B hB) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [normalize, Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [Finset.mem_image]
    refine ⟨a' + b', Finset.add_mem_add ha' hb', ?_⟩
    abel
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Finset.mem_add] at hz ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    refine ⟨a - lexMin A hA, ?_, b - lexMin B hB, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    · exact Finset.mem_image.2 ⟨b, hb, rfl⟩
    · abel

/-- The sum of the translates of `A` and `B` has as many points as `A + B`. -/
lemma normalize_add_card (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty)
    (hB : B.Nonempty) : (normalize A hA + normalize B hB).card = (A + B).card := by
  rw [normalize_add, Finset.card_image_of_injective]
  intro x y hxy
  exact sub_left_injective hxy

/-- The sum of the translates of `A` and `B` has the affine dimension of `A + B`. -/
lemma normalize_add_dim (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    finsetAffineDim (normalize A hA + normalize B hB) = finsetAffineDim (A + B) := by
  rw [normalize_add, finsetAffineDim_image_sub]

end Normalize

end SumOfSetsInSeveralDimensions
