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

Let `A` and `B` be finite subsets of a commutative monoid with `B` nonempty and `|B| ≤ |A|`, and
let `f` be a Freiman isomorphism of order `2` from `A ∪ B` onto a subset of `ℝ^r` of affine
dimension `r`. Then `f` sends `A` and `B` to sets `A'` and `B'` with `|A'| = |A|`, `|B'| = |B|` and
`|A' + B'| = |A + B|`, and `A' + B'` has affine dimension at least `r - 1`. Ruzsa's theorem then
gives `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. A Freiman model in `ℚ^r` is
one in `ℝ^r`, so this holds when `r ≥ 1` is the Freiman dimension of `A ∪ B`.

## Main statements

* `card_add_sum_min_le_card_add_of_isAddFreimanIso`: the bound above.
* `card_add_sum_min_le_of_freimanDim_union`: the bound for `r` the Freiman dimension of `A ∪ B`.
* `card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union`: the weaker bound
  `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`.
* `le_two_mul_sub_one_of_isAddFreimanIso`: if `|X + X| ≤ κ * |X|` for a real `κ`, then a Freiman
  model of `X` in `ℝ^r` of affine dimension `r` has `r ≤ 2 * κ - 1`.
* `freimanDim_le_two_mul_sub_one_of_card_add_le`: if `|X + X| ≤ κ * |X|`, then
  `freimanDim X ≤ 2 * κ - 1`.
-/

@[expose] public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

noncomputable section

lemma rationalVectorToReal_injective {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) :=
  Rat.cast_injective.comp_left

lemma rationalVectorToReal_add {d : ℕ} (x y : Fin d → ℚ) :
    rationalVectorToReal (x + y) = rationalVectorToReal x + rationalVectorToReal y := by
  ext i
  simp [rationalVectorToReal]

/-- A Freiman isomorphism into `ℚ^d` followed by the inclusion of `ℚ^d` into `ℝ^d` is a Freiman
isomorphism into `ℝ^d`. -/
lemma isAddFreimanIso_rationalVectorToReal_comp {G : Type*} [AddCommMonoid G] {d : ℕ}
    {X : Finset G} {f : G → (Fin d → ℚ)}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f) :
    IsAddFreimanIso 2 (X : Set G) (X.image (rationalVectorToReal ∘ f) : Set (Fin d → ℝ))
      (rationalVectorToReal ∘ f) := by
  rw [isAddFreimanIso_two] at hf ⊢
  refine ⟨?_, fun a ha b hb c hc e he ↦ ?_⟩
  · rw [coe_image]
    exact (rationalVectorToReal_injective.comp_injOn hf.1.injOn).bijOn_image
  · simp only [Function.comp, ← rationalVectorToReal_add, rationalVectorToReal_injective.eq_iff]
    exact hf.2 a ha b hb c hc e he

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
    obtain ⟨hy, hfy⟩ := (mem_image.mp (mem_image_of_mem f hx)).choose_spec
    exact ⟨f x, mem_image_of_mem f hx, (h _ hy _ hx).1 hfy⟩

/-- A Freiman isomorphism of order `2` on `X` preserves the size of `A + B` for `A, B ⊆ X`. -/
lemma card_add_image_of_isAddFreimanIso {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H] {X A B : Finset G} {f : G → H}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set H) f) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(A.image f + B.image f) = #(A + B) := by
  rw [add_def, add_def, ← prodMap_image_product, image_image]
  apply card_image_eq_of_kernel_iff
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  obtain ⟨ha, hb⟩ := mem_product.1 hab
  obtain ⟨ha', hb'⟩ := mem_product.1 hab'
  exact hf.add_eq_add (hAX ha) (hBX hb) (hAX ha') (hBX hb')

/-- **Ruzsa's theorem for a Freiman model.** Let `A` and `B` be finite subsets of a commutative
monoid with `B` nonempty and `|B| ≤ |A|`, and let `f` be a Freiman isomorphism of order `2` from
`A ∪ B` onto a subset of `ℝ^r` of affine dimension `r`. Then
`|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_card_add_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ} (hB : B.Nonempty)
    (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : finsetAffineDim ((A ∪ B).image f) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  have hcard {S : Finset G} (hS : S ⊆ A ∪ B) : #(S.image f) = #S :=
    card_image_of_injOn (hf.bijOn.injOn.mono (coe_subset.2 hS))
  have hA : A.Nonempty := card_pos.1 (hB.card_pos.trans_le hBA)
  have h := card_add_sum_min_le_card_add_of_le (d := r - 1) (hB.image f)
    (by rwa [hcard subset_union_left, hcard subset_union_right])
    (by grind [image_union, finsetAffineDim_union_le_sum_add_one (hA.image f) (hB.image f)])
  rwa [hcard subset_union_left, hcard subset_union_right,
    card_add_image_of_isAddFreimanIso hf subset_union_left subset_union_right] at h

/-- Ruzsa's theorem for a Freiman model, with the affine dimension of the model written as the
dimension of the span of its differences. -/
theorem card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA hf
    ((finsetAffineDim_eq_finrank_span_sub _).trans hdim)

private lemma sub_one_mul_le_choose_add_choose (b r : ℕ) :
    (r - 1) * b ≤ b.choose 2 + (r + 1).choose 2 := by
  obtain _ | r := r
  · simp
  · rw [← Nat.cast_le (α := ℚ), Nat.cast_add, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    nlinarith [sq_nonneg ((r : ℚ) + 1 - b), (Nat.cast_nonneg r : (0 : ℚ) ≤ r),
      (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]

private lemma sum_Ico_one_min_eq_choose {r : ℕ} (hr : 1 ≤ r) :
    ∑ s ∈ Ico 1 r, min (r - 1) s = r.choose 2 := by
  rw [sum_congr rfl (g := id) (by grind), ← Nat.sub_add_cancel hr, Ico_add_one_right_eq_Icc]
  simpa using Nat.sum_Icc_choose (r - 1) 1

private lemma sum_Ico_min_eq_mul {b r : ℕ} :
    ∑ s ∈ Ico r b, min (r - 1) s = (b - r) * (r - 1) := by
  rw [sum_congr rfl (g := fun _ ↦ r - 1) (by grind)]
  simp

private lemma sum_Icc_min_sub {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) = r.choose 2 + (b - r) * (r - 1) := by
  rw [← sum_Ico_one_min_eq_choose hr, ← sum_Ico_min_eq_mul, sum_Ico_consecutive _ hr hrb,
    ← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel (hr.trans hrb)]
  convert sum_Ico_reflect (fun s ↦ min (r - 1) s) 1 (Nat.le_succ b) using 3 <;> grind

private lemma add_one_le_two_mul_of_add_choose_add_le {b r : ℕ} {κ : ℝ} (hr : 1 ≤ r)
    (hrb : r ≤ b) (hbound : ((b + (r.choose 2 + (b - r) * (r - 1)) : ℕ) : ℝ) ≤ κ * b) :
    (r : ℝ) + 1 ≤ 2 * κ := by
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_sub hrb,
    Nat.cast_pred hr] at hbound
  nlinarith [mul_nonneg (sub_nonneg.2 (mod_cast hrb : (r : ℝ) ≤ b))
    (sub_nonneg.2 (mod_cast hr : (1 : ℝ) ≤ r)), (mod_cast hr.trans hrb : (1 : ℝ) ≤ b)]

/-- In a cancellative monoid, `|X + X| ≤ κ * |X|` for a nonempty `X` forces `1 ≤ κ`. -/
private lemma one_le_of_card_add_le {G : Type*} [DecidableEq G] [AddCancelCommMonoid G] {κ : ℝ}
    {X : Finset G} (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X) : 1 ≤ κ := by
  have h : (#X : ℝ) ≤ κ * #X := (Nat.cast_le.2 (card_le_card_add_left hX)).trans hXX
  nlinarith [(mod_cast hX.card_pos : (0 : ℝ) < #X)]

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X` and `f` is a Freiman isomorphism of order `2` from
`X` onto a subset of `ℝ^r` of affine dimension `r`, then `r ≤ 2 * κ - 1`. -/
theorem le_two_mul_sub_one_of_isAddFreimanIso {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : finsetAffineDim (X.image f) = r) : (r : ℝ) ≤ 2 * κ - 1 := by
  obtain rfl | hr := r.eq_zero_or_pos
  · grind [one_le_of_card_add_le hX hXX]
  have hrX : r ≤ #X := by
    grind [finsetAffineDim_add_one_le_card (hX.image f), card_image_of_injOn hf.bijOn.injOn]
  have h := card_add_sum_min_le_card_add_of_isAddFreimanIso hX le_rfl (by rwa [union_self])
    (by rwa [union_self])
  rw [sum_Icc_min_sub hr hrX] at h
  linarith [add_one_le_two_mul_of_add_choose_add_le hr hrX ((Nat.cast_le.2 h).trans hXX)]

/-- The bound `r ≤ 2 * κ - 1` for a Freiman model, with the affine dimension of the model written
as the dimension of the span of its differences. -/
theorem le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 :=
  le_two_mul_sub_one_of_isAddFreimanIso hX hXX hf
    ((finsetAffineDim_eq_finrank_span_sub _).trans hdim)

lemma sub_mul_sub_choose_le_sum_min (b r : ℕ) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min (r - 1) (b - t) := by
  rw [Nat.sub_le_iff_le_add]
  obtain hrb | hbr := le_total r b
  · obtain rfl | hr := r.eq_zero_or_pos
    · simp
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hrb
      rw [sum_Icc_min_sub hr hrb, Nat.add_sub_cancel_left, mul_add]
      linarith [sub_one_mul_le_choose_add_choose r r, mul_comm c (r - 1)]
  · obtain rfl | hb := b.eq_zero_or_pos
    · simp
    · refine (sub_one_mul_le_choose_add_choose b r).trans ?_
      rw [← add_zero (b.choose 2), ← zero_mul (b - 1), ← Nat.sub_self b,
        ← sum_Icc_min_sub hb le_rfl]
      gcongr

lemma sub_mul_sub_choose_le_sum_min_of_le {a b r d : ℕ} (hba : b ≤ a) (hrd : r ≤ d + 1) :
    (r - 1) * b - (r + 1).choose 2 ≤ ∑ t ∈ Icc 1 (b - 1), min d (a - t) := by
  refine (sub_mul_sub_choose_le_sum_min b r).trans ?_
  apply sum_le_sum
  grind

/-- Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
dimension of `A ∪ B`. Then `|A| + ∑ t ∈ {1, …, |B| - 1}, min (r - 1) (|A| - t) ≤ |A + B|`. -/
theorem card_add_sum_min_le_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {A B : Finset G} (hr : 1 ≤ r) (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hdim : freimanDim (A ∪ B) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) := by
  classical
  obtain ⟨f, hf, haff⟩ := Nat.findGreatest_of_ne_zero hdim (Nat.ne_of_gt hr)
  exact card_add_sum_min_le_card_add_of_isAddFreimanIso hB hBA
    (isAddFreimanIso_rationalVectorToReal_comp hf) (by rwa [← image_image])

/-- Let `A` and `B` be finite with `B` nonempty and `|B| ≤ |A|`, and let `r ≥ 1` be the Freiman
dimension of `A ∪ B`. Then `|A| + (r - 1) * |B| - (r + 1).choose 2 ≤ |A + B|`. -/
lemma card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union
    {G : Type*} [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} (hr : 1 ≤ r)
    (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : freimanDim (A ∪ B) = r) :
    #A + (r - 1) * #B - (r + 1).choose 2 ≤ #(A + B) := by
  grind [card_add_sum_min_le_of_freimanDim_union hr hB hBA hdim,
    sub_mul_sub_choose_le_sum_min_of_le (r := r) (d := r - 1) hBA (by grind)]

/-- If `|X + X| ≤ κ * |X|` for a nonempty `X`, then `X` has Freiman dimension at most
`2 * κ - 1`. -/
theorem freimanDim_le_two_mul_sub_one_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) : (freimanDim X : ℝ) ≤ 2 * κ - 1 := by
  classical
  obtain hr | hr := (freimanDim X).eq_zero_or_pos
  · rw [hr, Nat.cast_zero]
    linarith [one_le_of_card_add_le hX hXX]
  obtain ⟨f, hf, haff⟩ := Nat.findGreatest_of_ne_zero (rfl : freimanDim X = _) hr.ne'
  exact le_two_mul_sub_one_of_isAddFreimanIso hX hXX (isAddFreimanIso_rationalVectorToReal_comp hf)
    (by rwa [← image_image])

end

end SumOfSetsInSeveralDimensions
