# Every Separable Metric Space Extends to an Extreme One

Paper and Lean 4 formalization.

**Theorem.** Every separable bounded-by-one pseudometric space `(X, d)` is the restriction
of an extreme point of the metric body of some `X̃ ⊇ X` with `X̃ \ X` countable.

For finite `X` the metric body is a rational polytope, so its extreme points have rational
distances and satisfy the rigidity that comes with lying on many facets. No such restriction
survives passage to infinite `X`: the local structure of an extreme point may be arbitrary,
irrational distances included.

## Contents

| path | |
|---|---|
| `paper/separable-extreme.tex`, `.pdf` | the paper |
| `lean/` | the Lake project (Lean 4, Mathlib) |
| `VERIFICATION.md` | verification report and coverage ledger |
| `docs/` | the commissions the formalization was written against |
| `scripts/` | the checks CI runs |

## Verification status

Sections 2-6 are fully formalized, with no hypotheses beyond those the paper states;
Section 7 (recovery and the reduction from graph isomorphism) is formalized on the
countable carriers, for simple graphs, with two marked exceptions: the two-line
completion lemma is prose only (its inputs are formalized), and the completeness of the
graph-space carriers is proved in ingredients. Descriptive-set-theoretic inputs
(Gao-Kechris, Hjorth) are cited, not formalized. The paper's Section 8 ledger and
`VERIFICATION.md` record every row. Theorem 1.1 appears in two forms: `separable_extends_to_extreme'`, and
`separable_extends_to_extremePoint'` against Mathlib's `Set.extremePoints` for the convex
set of bounded-by-one pseudometrics. Section 7 of the paper carries the result-by-result
ledger; `VERIFICATION.md` carries the longer version.

Four statements are recorded in the development as deliberately false, each guarding a
hypothesis the proofs consume, and each refuted there by an explicit counterexample.

## Building

```
cd lean
lake exe cache get
lake build
```

The axiom audit is `#print axioms` on the headline theorems, in
`lean/RequestProject/Main.lean`:

```
./scripts/check_sorry.sh
./scripts/audit_axioms.sh
```

CI runs both on every push, together with the LaTeX build.

## Companion papers

This paper is one of four drawn from E. R. Kehoe's 2019 doctoral dissertation,
*Pseudometrics, the Complex of Ultrametrics, and Iterated Cycle Structures*
(University of New Hampshire, <https://scholars.unh.edu/dissertation/2451>). It cites the
companion paper on the metric cone for the generalized bowtie metrics; the formalization
here does not depend on it, proving Proposition 5.1 directly.

## License

To be chosen before the first release. Add a `LICENSE` file and record it in
`CITATION.cff`.
