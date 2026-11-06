# Sum of sets in several dimensions

Lean 4 proof of the results of Imre Z. Ruzsa,
[*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969), Combinatorica 14
(1994), 485–490: a lower bound for sumsets in $\mathbb{R}^D$, the fact that it is the least size
of such a sumset, and its closed form, the asymmetric form of Freiman's lemma.

## Results

The affine dimension of a finite set $S \subseteq \mathbb{R}^D$ is the dimension of the direction
of its affine span, that is, of the subspace spanned by the differences of the points of $S$.

**Theorem 1** (`SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_finrank_span_sub_eq`).
Let $A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and
$\left\lvert B\right\rvert \le \left\lvert A\right\rvert$. If $d$ is the affine dimension of
$A + B$, then

$$\left\lvert A + B\right\rvert \ge \left\lvert A\right\rvert +
\sum_{t=1}^{\left\lvert B\right\rvert-1} \min(d, \left\lvert A\right\rvert - t).$$

**Corollary 1.1**
(`SumOfSetsInSeveralDimensions.card_add_mul_card_le_card_add_add_of_le_finrank_span_sub`). Let
$A, B \subseteq \mathbb{R}^D$ be finite sets with $B$ nonempty and
$\left\lvert B\right\rvert \le \left\lvert A\right\rvert$. If $d$ is at most the affine dimension of
$A + B$, then

$$\left\lvert A\right\rvert + d\left\lvert B\right\rvert \le
\left\lvert A + B\right\rvert + \frac{d(d+1)}{2}.$$

**Theorem 2** (`SumOfSetsInSeveralDimensions.sInf_card_add_eq_add_sum_min` and
`SumOfSetsInSeveralDimensions.sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min`). Let
$d \ge 1$, $1 \le m \le n$ and $n \ge d + 1$. The least size of $A + B$ over sets
$A, B \subseteq \mathbb{R}^d$ with $\left\lvert A\right\rvert = m$, $\left\lvert B\right\rvert = n$
and $A + B$ of affine dimension $d$ is

$$G_d(m, n) = n + \sum_{j=1}^{m-1} \min(d, n - j),$$

and so is the least size of $A + B$ with $B$ of affine dimension $d$.

Three results formalized here are not in the paper. A Freiman model of a finite subset $X$ of a
commutative monoid is a Freiman isomorphism of order 2 from $X$ onto a set in $\mathbb{R}^r$ of
affine dimension $r$.

**Theorem 1 for Freiman models**
(`SumOfSetsInSeveralDimensions.card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq`).
Let $A, B$ be finite subsets of a commutative monoid with $B$ nonempty and
$\left\lvert B\right\rvert \le \left\lvert A\right\rvert$. If $A \cup B$ has a Freiman model in
$\mathbb{R}^r$, then

$$\left\lvert A + B\right\rvert \ge \left\lvert A\right\rvert +
\sum_{t=1}^{\left\lvert B\right\rvert-1} \min(r - 1, \left\lvert A\right\rvert - t).$$

**The Freiman dimension and the doubling**
(`SumOfSetsInSeveralDimensions.le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq`). Let
$X$ be a nonempty finite subset of a cancellative commutative monoid with
$\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$ for a real $\kappa$. If $X$ has
a Freiman model in $\mathbb{R}^r$, then $r \le 2\kappa - 1$.

**Freiman's lemma for Freiman models**
(`SumOfSetsInSeveralDimensions.le_sub_one_add_mul_div_card_of_isAddFreimanIso_of_finrank_span_sub_eq`).
Under the same hypotheses,

$$r \le \kappa - 1 + \frac{\kappa(2\kappa - 1)}{\left\lvert X\right\rvert}.$$

The error term tends to $0$ as $\left\lvert X\right\rvert \to \infty$ with $\kappa$ fixed. The proof
applies Corollary 1.1 to the model of $X$ with $d = r$, which gives
$(r + 1)\left\lvert X\right\rvert - r(r + 1)/2 \le \kappa \left\lvert X\right\rvert$, and bounds
$r(r + 1)/2$ by $\kappa(2\kappa - 1)$ with $r \le 2\kappa - 1$.

The library states these seven theorems with the affine dimension of a set $S$ written as
`Module.finrank ℝ (Submodule.span ℝ (↑S - ↑S))`, the rank of the span of the differences.
[Challenge.lean](Challenge.lean) contains the same statements in terms of Mathlib, under the same
names with a prime and with `sorry` placeholders, and [Solution.lean](Solution.lean) proves each
of them by the library theorem. The library and the solution contain no `sorry`, and the theorems
depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

| Declaration | Statement |
| --- | --- |
| `Finset.affineDim S` | `Module.finrank ℝ (affineSpan ℝ ↑S).direction` |
| `minCardAdd_eq_sumsetCardLowerBound`, `minCardAddOfDimRight_eq_sumsetCardLowerBound` | Theorem 2, with the minima `F_d` and `F'_d` of the paper as definitions |
| `freimanDim X` | The Freiman dimension of a finite subset `X` of a commutative monoid |
| `card_add_sum_min_le_of_freimanDim_union` | Theorem 1 for `B` nonempty, `\|B\| ≤ \|A\|` and `freimanDim (A ∪ B) = r ≥ 1`, with `r - 1` in place of `d` |
| `freimanDim_le_two_mul_sub_one_of_card_add_le` | `freimanDim X ≤ 2 * κ - 1` if `X` is nonempty and `\|X + X\| ≤ κ * \|X\|`, for a real `κ` and a cancellative monoid |
| `freimanDim_le_sub_one_add_mul_div_card_of_card_add_le` | `freimanDim X ≤ κ - 1 + κ * (2 * κ - 1) / \|X\|` under the same hypotheses |

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
| `FreimanDimensionSumsetBounds.lean` | Theorem 1 for Freiman models and sets of given Freiman dimension, and the bounds `2 * κ - 1` and `κ - 1 + κ * (2 * κ - 1) / \|X\|` |

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
