/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import SumOfSetsInSeveralDimensions.FreimanDimension
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import SumOfSetsInSeveralDimensions.AffineDimSumset
import SumOfSetsInSeveralDimensions.LowerBound

/-!
# Sumset bounds from the Freiman dimension

Let `A` and `B` be finite nonempty subsets of a commutative monoid with `|B| ≤ |A|`, and let
`r ≥ 1` be the Freiman dimension of `A ∪ B`. A Freiman model of `A ∪ B` of affine dimension `r` in
`ℚ^r` sends `A` and `B` to sets `A'` and `B'` in `ℝ^r` with `|A'| = |A|`, `|B'| = |B|` and
`|A' + B'| = |A + B|`, and `A' + B'` has affine dimension at least `r - 1`. Ruzsa's lower bound
for sumsets in several dimensions then gives

`|A| + ∑ t ∈ [1, |B| - 1], min (r - 1) (|A| - t) ≤ |A + B|`.

## Main definitions

* `freimanRealImage f S`: the image in `ℝ^d` of `S` under a map `f` into `ℚ^d`.

## Main statements

* `card_add_sum_min_le_of_freimanDim_union`: the bound above.
* `card_add_lower_bound_of_freimanDim_union`: the weaker bound
  `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`.
* `freimanDim_le_two_mul_sub_one_of_card_add_le`: if `|X + X| ≤ κ * |X|`, then
  `freimanDim X ≤ 2 * κ - 1`.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise Affine

noncomputable section

/-- The image in `ℝ^d` of a finite set `S` under a map `f` into `ℚ^d`. -/
def freimanRealImage {G : Type*} [DecidableEq G] {d : ℕ}
    (f : G → (Fin d → ℚ)) (S : Finset G) : Finset (Fin d → ℝ) :=
  (S.image f).image rationalVectorToReal

lemma rationalVectorToReal_injective {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) :=
  fun _ _ h ↦ funext fun i ↦ Rat.cast_injective (congrFun h i)

lemma rationalVectorToReal_add {d : ℕ} (x y : Fin d → ℚ) :
    rationalVectorToReal (x + y) = rationalVectorToReal x + rationalVectorToReal y := by
  ext i
  simp [rationalVectorToReal]

/-- Two maps with the same fibres on `s` have images of `s` of the same size. -/
lemma card_image_eq_of_kernel_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ}
    (h : ∀ x ∈ s, ∀ y ∈ s, (f x = f y ↔ g x = g y)) :
    #(s.image f) = #(s.image g) := by
  refine card_bij (fun b hb ↦ g (mem_image.mp hb).choose) ?_ ?_ ?_
  · intro b hb
    exact mem_image_of_mem g (mem_image.mp hb).choose_spec.1
  · intro b₁ hb₁ b₂ hb₂ hgb
    obtain ⟨hx₁, hfb₁⟩ := (mem_image.mp hb₁).choose_spec
    obtain ⟨hx₂, hfb₂⟩ := (mem_image.mp hb₂).choose_spec
    exact hfb₁ ▸ hfb₂ ▸ (h _ hx₁ _ hx₂).2 hgb
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    have hfx := mem_image_of_mem f hx
    obtain ⟨hy, hfy⟩ := (mem_image.mp hfx).choose_spec
    exact ⟨f x, hfx, (h _ hy _ hx).1 hfy⟩

private lemma card_freimanRealImage {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) : #(freimanRealImage f A) = #A := by
  rw [freimanRealImage, card_image_of_injective _ rationalVectorToReal_injective,
    card_image_of_injOn (hiso.bijOn.injOn.mono (coe_subset.2 hAX))]

private lemma freimanRealImage_nonempty {G : Type*} [DecidableEq G] {d : ℕ}
    {f : G → (Fin d → ℚ)} {S : Finset G} (hS : S.Nonempty) : (freimanRealImage f S).Nonempty :=
  (hS.image f).image _

/-- A Freiman isomorphism of order `2` on `X` preserves the size of `A + B` for `A, B ⊆ X`. -/
lemma card_add_freimanRealImage {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(freimanRealImage f A + freimanRealImage f B) = #(A + B) := by
  rw [freimanRealImage, freimanRealImage, image_image, image_image, add_def, add_def,
    ← prodMap_image_product, image_image]
  apply card_image_eq_of_kernel_iff
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  rw [mem_product] at hab hab'
  simp only [Function.comp, Prod.map, ← rationalVectorToReal_add,
    rationalVectorToReal_injective.eq_iff]
  exact hiso.add_eq_add (hAX hab.1) (hBX hab.2) (hAX hab'.1) (hBX hab'.2)

/-- A Freiman isomorphism on `X` preserves the comparison `|B| ≤ |A|` for `A, B ⊆ X`. -/
lemma card_freimanRealImage_le {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #B ≤ #A → #(freimanRealImage f B) ≤ #(freimanRealImage f A) := by
  rw [card_freimanRealImage hiso hAX, card_freimanRealImage hiso hBX]
  exact id

/-- If the model of `X ⊆ A ∪ B` has affine dimension `r`, then the model of `A + B` has affine
dimension at least `r - 1`. -/
lemma freimanDim_le_sumsetAffineDim_add_one
    {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (haff : finsetAffineDim ((X.image f).image rationalVectorToReal) = r) (hX : X ⊆ A ∪ B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    r ≤ finsetAffineDim (freimanRealImage f A + freimanRealImage f B) + 1 := by
  refine haff.symm.trans_le ((finsetAffineDim_mono ?_).trans (finsetAffineDim_union_le_sum_add_one
    _ _ (freimanRealImage_nonempty hA) (freimanRealImage_nonempty hB)))
  rw [freimanRealImage, freimanRealImage, ← image_union, ← image_union]
  exact image_subset_image (image_subset_image hX)

private lemma sub_one_mul_le_choose_add_choose (b r : ℕ) :
    (r - 1) * b ≤ b.choose 2 + (r + 1).choose 2 := by
  obtain _ | r := r
  · simp
  · rw [← Nat.cast_le (α := ℚ), Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    nlinarith [sq_nonneg ((r : ℚ) + 1 - b), (Nat.cast_nonneg r : (0 : ℚ) ≤ r),
      (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]

private lemma sum_Icc_min_sub {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) = r.choose 2 + (b - r) * (r - 1) := by
  have h₁ : ∑ s ∈ Ico 1 r, min (r - 1) s = r.choose 2 := by
    rw [sum_congr rfl (g := id) (by grind), ← Nat.sub_add_cancel hr,
      Finset.Ico_add_one_right_eq_Icc]
    simpa using Nat.sum_Icc_choose (r - 1) 1
  have h₂ : ∑ s ∈ Ico r b, min (r - 1) s = (b - r) * (r - 1) := by
    rw [sum_congr rfl (g := fun _ ↦ r - 1) (by grind)]
    simp
  rw [← h₁, ← h₂, sum_Ico_consecutive _ hr hrb, ← Finset.Ico_add_one_right_eq_Icc,
    Nat.sub_add_cancel (hr.trans hrb)]
  convert sum_Ico_reflect (fun s ↦ min (r - 1) s) 1 (Nat.le_succ b) using 3 <;> grind

private lemma lt_two_mul_of_add_choose_add_le {b r κ : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b)
    (hbound : b + (r.choose 2 + (b - r) * (r - 1)) ≤ κ * b) : r < 2 * κ := by
  by_contra! hκ
  have h : (b : ℚ) + (r * (r - 1) / 2 + (b - r) * (r - 1)) ≤ κ * b := by
    rw [← Nat.cast_choose_two, ← Nat.cast_sub hrb, ← Nat.cast_pred hr]
    exact_mod_cast hbound
  have hr' : (1 : ℚ) ≤ r := mod_cast hr
  have hrb' : (r : ℚ) ≤ b := mod_cast hrb
  have hκ' : (2 * κ : ℚ) ≤ r := mod_cast hκ
  nlinarith [mul_nonneg (sub_nonneg.2 hκ') (le_trans (by linarith) hrb'),
    mul_nonneg (le_trans zero_le_one hr') (sub_nonneg.2 hrb')]

lemma sub_mul_sub_choose_le_sum_min (b r : ℕ) :
    (r - 1) * b - Nat.choose (r + 1) 2 ≤ ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) := by
  rw [Nat.sub_le_iff_le_add]
  obtain hrb | hbr := le_total r b
  · obtain rfl | hr := r.eq_zero_or_pos
    · simp
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hrb
      rw [sum_Icc_min_sub hr hrb, Nat.add_sub_cancel_left, mul_add]
      linarith [sub_one_mul_le_choose_add_choose r r, mul_comm c (r - 1)]
  · obtain rfl | hb := b.eq_zero_or_pos
    · simp
    · have h := sum_Icc_min_sub hb le_rfl
      rw [Nat.sub_self, zero_mul, add_zero] at h
      refine (sub_one_mul_le_choose_add_choose b r).trans ?_
      rw [← h]
      gcongr

lemma sub_mul_sub_choose_le_sum_min_of_le {a b r d : ℕ} (hba : b ≤ a) (hrd : r ≤ d + 1) :
    (r - 1) * b - Nat.choose (r + 1) 2 ≤ ∑ t ∈ Icc 1 (b - 1), min d (a - t) := by
  refine (sub_mul_sub_choose_le_sum_min b r).trans (sum_le_sum fun t _ ↦ ?_)
  grind

/-- The bound `|A'| + ∑ t ∈ [1, |B'| - 1], min d (|A'| - t) ≤ |A' + B'|` for the images `A'` and
`B'` of `A` and `B` in a Freiman model gives
`|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|` when `r ≤ d + 1`. -/
lemma card_add_lower_bound_of_freimanModel {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r d : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hBA : #B ≤ #A)
    (hrd : r ≤ d + 1)
    (hasym :
      #(freimanRealImage f A) +
          ∑ t ∈ Icc 1 (#(freimanRealImage f B) - 1), min d (#(freimanRealImage f A) - t) ≤
        #(freimanRealImage f A + freimanRealImage f B)) :
    #A + (r - 1) * #B - Nat.choose (r + 1) 2 ≤ #(A + B) := by
  rw [card_freimanRealImage hiso hAX, card_freimanRealImage hiso hBX,
    card_add_freimanRealImage hiso hAX hBX] at hasym
  grind [sub_mul_sub_choose_le_sum_min_of_le hBA hrd]

/-- Let `A` and `B` be nonempty with `|B| ≤ |A|` and let `r ≥ 1` be the Freiman dimension of
`A ∪ B`. Then `|A| + ∑ t ∈ [1, |B| - 1], min (r - 1) (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (r : ℕ) (A B : Finset G) (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  classical
  obtain ⟨f, hiso, haff⟩ := Nat.findGreatest_of_ne_zero hdim (Nat.ne_of_gt hr)
  have h := card_add_sum_min_le_card_add_of_le (d := r - 1) _ _
    (freimanRealImage_nonempty (f := f) hB)
    (card_freimanRealImage_le hiso subset_union_left subset_union_right hBA)
    (Nat.sub_le_of_le_add (freimanDim_le_sumsetAffineDim_add_one haff Subset.rfl hA hB))
  rwa [card_freimanRealImage hiso subset_union_left, card_freimanRealImage hiso subset_union_right,
    card_add_freimanRealImage hiso subset_union_left subset_union_right] at h

/-- Let `A` and `B` be nonempty with `|B| ≤ |A|` and let `r ≥ 1` be the Freiman dimension of
`A ∪ B`. Then `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`. -/
lemma card_add_lower_bound_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (r : ℕ) (A B : Finset G) (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + (r - 1) * #B - Nat.choose (r + 1) 2 ≤ #(A + B) := by
  have h := card_add_sum_min_le_of_freimanDim_union r A B hr hA hB hBA hdim
  have h' := sub_mul_sub_choose_le_sum_min_of_le (r := r) (d := r - 1) hBA (by grind)
  grind

/-- If `|X + X| ≤ κ * |X|`, then `X` has Freiman dimension at most `2 * κ - 1`. -/
theorem freimanDim_le_two_mul_sub_one_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {κ : ℕ} (X : Finset G) (hXX : #(X + X) ≤ κ * #X) :
    freimanDim X ≤ 2 * κ - 1 := by
  classical
  have hrX : freimanDim X ≤ #X := Nat.findGreatest_le #X
  obtain hr | hr := (freimanDim X).eq_zero_or_pos
  · simp [hr]
  have hX : X.Nonempty := card_pos.mp (hr.trans_le hrX)
  refine Nat.le_sub_one_of_lt (lt_two_mul_of_add_choose_add_le hr hrX ?_)
  rw [← sum_Icc_min_sub hr hrX]
  exact (card_add_sum_min_le_of_freimanDim_union _ X X hr hX hX le_rfl
    (by rw [union_self])).trans hXX

end

end SumOfSetsInSeveralDimensions
