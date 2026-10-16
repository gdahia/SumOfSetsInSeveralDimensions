# Sum of sets in several dimensions

Lean 4 proof of the lower bound for sumsets in $\mathbb{R}^D$ of Imre Z. Ruzsa,
[*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969), Combinatorica 14
(1994), 485–490, and of its closed form, the asymmetric form of Freiman's lemma.

## Results

The affine dimension of a finite set $S \subseteq \mathbb{R}^D$ is the dimension of the direction
of its affine span, that is, of the subspace spanned by the differences of the points of $S$.

**Ruzsa's theorem**
(`SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq`). Let
$A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and $|B| \le |A|$, and let $d$ be
the affine dimension of $A + B$. Then

$$|A + B| \ge |A| + \sum_{t=1}^{|B|-1} \min(d, |A| - t).$$

**The asymmetric form of Freiman's lemma**
(`SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`). Let
$A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and $|B| \le |A|$, and let $d$ be
at most the affine dimension of $A + B$. Then

$$|A| + d|B| \le |A + B| + \frac{d(d+1)}{2}.$$

[Solution.lean](Solution.lean) proves both. [Challenge.lean](Challenge.lean) contains the same
statements in terms of Mathlib, with the affine dimension of `A + B` written as
`Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B)))`, the rank of the span of the
differences, and with `sorry` placeholders. The library and the solution contain no `sorry`, and
the theorems depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library states the two theorems with the definition `finsetAffineDim`, as
`card_add_sum_min_le_card_add` and `card_add_mul_card_le_card_add_add`. Its other statements
are the following.

| Declaration | Statement |
| --- | --- |
| `finsetAffineDim S` | `Module.finrank ℝ (affineSpan ℝ ↑S).direction` |
| `finsetAffineDim_eq_finrank_vectorSpan` | `finsetAffineDim S = Module.finrank ℝ (vectorSpan ℝ ↑S)` |
| `finsetAffineDim_mono` | `finsetAffineDim S ≤ finsetAffineDim T` if `S ⊆ T` |
| `finsetAffineDim_le` | `finsetAffineDim S ≤ D` |
| `finsetAffineDim_vadd_finset`, `finsetAffineDim_image_add_left`, `finsetAffineDim_image_add_right`, `finsetAffineDim_image_sub` | A translate of `S` has the affine dimension of `S` |
| `finsetAffineDim_add_one_le_card` | `finsetAffineDim S + 1 ≤ \|S\|` if `S` is nonempty |
| `finsetAffineDim_le_finsetAffineDim_add_right`, `finsetAffineDim_le_finsetAffineDim_add_left` | `A` and `B` have affine dimension at most that of `A + B` if `B`, respectively `A`, is nonempty |
| `finsetAffineDim_union_le_sum_add_one` | `finsetAffineDim (A ∪ B) ≤ finsetAffineDim (A + B) + 1` if `A` and `B` are nonempty |
| `card_add_sum_min_le_card_add_of_le` | Ruzsa's theorem for every `d ≤ finsetAffineDim (A + B)` |
| `two_mul_card_add_mul_card_le` | `2 * (\|A\| + d * \|B\|) ≤ 2 * \|A + B\| + d * (d + 1)` |
| `card_add_mul_card_sub_le_card_add` | `\|A\| + d * \|B\| - d * (d + 1) / 2 ≤ \|A + B\|` in `ℝ` |
| `max_card_add_mul_min_card_le_card_add_add` | The closed form for nonempty `A` and `B`, with `max \|A\| \|B\|` and `min \|A\| \|B\|` in place of `\|A\|` and `\|B\|` |

## Files

| Files in `SumOfSetsInSeveralDimensions/` | Contents |
| --- | --- |
| `AffineDim.lean` | The affine dimension of a finite set, monotonicity, translations |
| `AffineDimSumset.lean` | The affine dimension of `A + B` against those of `A`, `B` and `A ∪ B` |
| `LowerBoundFunction.lean` | The bound as a function of $d$, $\lvert B \rvert$ and $\lvert A \rvert$, and the inequalities for the induction |
| `Normalize.lean` | Translation of a set by its lexicographically least element |
| `GeometricDeletion.lean` | The four cases for removing `0` from the translated summands |
| `LowerBound.lean` | Ruzsa's theorem |
| `ClosedForm.lean` | The closed form |

The Lean proof was not compared with the proof in Ruzsa's paper.
[formalization.yaml](formalization.yaml) records the differences from the paper, the
scope, and the use of AI coding agents.

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
