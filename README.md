# Sum of sets in several dimensions

Lean 4 proof of the results of Imre Z. Ruzsa,
[*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969), Combinatorica 14
(1994), 485–490: a lower bound for sumsets in $\mathbb{R}^D$, the fact that it is the least size
of such a sumset, and its closed form, the asymmetric form of Freiman's lemma.

## Results

The affine dimension of a finite set $S \subseteq \mathbb{R}^D$ is the dimension of the direction
of its affine span, that is, of the subspace spanned by the differences of the points of $S$.

**Theorem 1**
(`SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq`). Let
$A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and $|B| \le |A|$, and let $d$ be
the affine dimension of $A + B$. Then

$$|A + B| \ge |A| + \sum_{t=1}^{|B|-1} \min(d, |A| - t).$$

**Corollary 1.1**
(`SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`). Let
$A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and $|B| \le |A|$, and let $d$ be
at most the affine dimension of $A + B$. Then

$$|A| + d|B| \le |A + B| + \frac{d(d+1)}{2}.$$

**Theorem 2** (`SumOfSetsInSeveralDimensions.sInf_card_add_eq_add_sum_min` and
`SumOfSetsInSeveralDimensions.sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min`). Let
$d \ge 1$, $1 \le m \le n$ and $n \ge d + 1$. The least size of $A + B$ over sets
$A, B \subseteq \mathbb{R}^d$ with $|A| = m$, $|B| = n$ and $A + B$ of affine dimension $d$ is

$$G_d(m, n) = n + \sum_{j=1}^{m-1} \min(d, n - j),$$

and so is the least size of $A + B$ with $B$ of affine dimension $d$. The paper also excludes the
pairs with $m \le n - m \le d$, but its construction covers them.

[Solution.lean](Solution.lean) proves these four statements. [Challenge.lean](Challenge.lean)
contains them in terms of Mathlib, with the affine dimension of a set $S$ written as
`Module.finrank ℝ (Submodule.span ℝ (↑S - ↑S))`, the rank of the span of the differences, and
with `sorry` placeholders. The library and the solution contain no `sorry`, and the theorems
depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library states the theorems with the definition `finsetAffineDim`. Its other statements are
the following.

| Declaration | Statement |
| --- | --- |
| `finsetAffineDim S` | `Module.finrank ℝ (affineSpan ℝ ↑S).direction` |
| `finsetAffineDim_eq_finrank_vectorSpan` | `finsetAffineDim S = Module.finrank ℝ (vectorSpan ℝ ↑S)` |
| `finsetAffineDim_mono` | `finsetAffineDim S ≤ finsetAffineDim T` if `S ⊆ T` |
| `finsetAffineDim_le` | `finsetAffineDim S ≤ D` |
| `finsetAffineDim_vadd_finset`, `finsetAffineDim_image_add_left`, `finsetAffineDim_image_add_right`, `finsetAffineDim_image_sub` | A translate of `S` has the affine dimension of `S` |
| `finsetAffineDim_add_one_le_card` | `finsetAffineDim S + 1 ≤ \|S\|` if `S` is nonempty |
| `finsetAffineDim_le_finsetAffineDim_add_right`, `finsetAffineDim_le_finsetAffineDim_add_left` | `A` and `B` have affine dimension at most that of `A + B` if `B`, respectively `A`, is nonempty |
| `finsetAffineDim_add_eq_of_left_eq` | `A + B` has affine dimension `D` if `A` has and `B` is nonempty |
| `finsetAffineDim_union_le_sum_add_one` | `finsetAffineDim (A ∪ B) ≤ finsetAffineDim (A + B) + 1` if `A` and `B` are nonempty |
| `geometric_deletion_cases` | Lemma 2.1 of the paper |
| `card_add_sum_min_le_card_add_of_le` | Theorem 1 for every `d ≤ finsetAffineDim (A + B)` |
| `two_mul_card_add_mul_card_le` | `2 * (\|A\| + d * \|B\|) ≤ 2 * \|A + B\| + d * (d + 1)` |
| `card_add_mul_card_sub_le_card_add` | `\|A\| + d * \|B\| - d * (d + 1) / 2 ≤ \|A + B\|` in `ℝ` |
| `max_card_add_mul_min_card_le_card_add_add` | Corollary 1.1 for nonempty `A` and `B`, with `max \|A\| \|B\|` and `min \|A\| \|B\|` in place of `\|A\|` and `\|B\|` |
| `sumsetCardLowerBound_of_add_le` | Formula (1.5): `G_d(m, n) = n + d * (m - 1)` if `m + d ≤ n + 1` |
| `two_mul_sumsetCardLowerBound_add_add`, `two_mul_sumsetCardLowerBound_add` | Formula (1.6), if `m ≤ n < m + d` and `d < n` |
| `two_mul_sumsetCardLowerBound_of_le` | Formula (1.7): `2 * G_d(m, n) = 2 * n + (m - 1) * (2 * n - m)` if `1 ≤ m ≤ n ≤ d` |
| `exists_card_add_eq_sumsetCardLowerBound` | The sets of Section 3, with `\|A + B\| = G_d(m, n)` |
| `minCardAdd_eq_sumsetCardLowerBound`, `minCardAddOfDimRight_eq_sumsetCardLowerBound` | Theorem 2, with the minima `F_d` and `F'_d` of the paper as definitions |
| `freimanDim X` | The Freiman dimension of a finite subset `X` of a commutative monoid |
| `card_add_sum_min_le_of_freimanDim_union` | Theorem 1 for nonempty `A`, `B` with `\|B\| ≤ \|A\|` and `freimanDim (A ∪ B) = r ≥ 1`, with `r - 1` in place of `d` |
| `card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union` | Under the same hypotheses, `\|A\| + (r - 1) * \|B\| - (r + 1).choose 2 ≤ \|A + B\|` |
| `freimanDim_le_two_mul_sub_one_of_card_add_le` | `freimanDim X ≤ 2 * κ - 1` if `\|X + X\| ≤ κ * \|X\|` |

## Files

| Files in `SumOfSetsInSeveralDimensions/` | Contents |
| --- | --- |
| `AffineDim.lean` | The affine dimension of a finite set, monotonicity, translations |
| `AffineDimSumset.lean` | The affine dimension of `A + B` against those of `A`, `B` and `A ∪ B` |
| `LowerBoundFunction.lean` | The bound $G_d(m, n)$ and the inequalities for the induction |
| `LowerBoundValues.lean` | The formulas (1.5), (1.6) and (1.7) for $G_d(m, n)$ |
| `Normalize.lean` | Translation of a set by its lexicographically least element |
| `GeometricDeletion.lean` | Lemma 2.1: the four cases for removing `0` from the translated summands |
| `LowerBound.lean` | Theorem 1 |
| `ClosedForm.lean` | Corollary 1.1 |
| `Construction.lean` | The sets of Section 3 |
| `MinCardAdd.lean` | Theorem 2 |
| `FreimanDimension.lean` | The Freiman dimension |
| `FreimanDimensionSumsetBounds.lean` | Theorem 1 for sets of given Freiman dimension, and `freimanDim X ≤ 2 * κ - 1` |

[formalization.yaml](formalization.yaml) records the differences from the paper, the scope, and
the use of AI coding agents.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
