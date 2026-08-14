# Aristotle commission — `separable-extreme`, Tier 5: discharge `hrat`

**Target.** Remove the last hypothesis. Prove Proposition 5.1 of `separable-extreme.tex`
inside the development, then restate `separable_extends_to_extreme` and
`exists_countable_extreme_realizing` without `hrat`.

**Prior art in the tarball is ground truth.** The Tier 1–4 development compiles and is not
to be modified except as §4 directs. The goal statement is exactly the current hypothesis:

```lean
theorem exists_finite_rigid_realizing (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
      IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)
```

**Standing caveat.** Nothing here was compiled by the author of this commission.

---

## 0. Census

The companion paper's Lean development is **not** in this tarball. If it is available in
your environment, check whether `thm:bowtie-general` and `thm:ray-to-point` are present in
reusable form — specifically whether the *value set* of the bowtie is exposed as a lemma
rather than buried in a proof, and whether the normalization matches `max = 1`. If both are
usable, transport is cheaper than §2 and you should say so and take that route. **If the
companion development is absent, proceed self-contained as below**; the argument does not
depend on it.

---

## 1. The construction, and a simplification worth taking

The companion paper's `cor:rational-distances` splits into two cases: `q = 2` uses
`B_{2,n-2}`, and `q ≥ 3` uses `B_{1,2,…,2,n-2q+1}`. **A single family covers every case**,
and it is the one to formalize:

> `B_b := B_{1,2,2,…,2}` with `k = b+1` cells, so `n = 2b + 1` points.

Cell sizes are `1` then `b` cells of size `2`. Interior cells are `P_2,…,P_b`, all of size
`2`; `k = b+1 ≥ 3` so the two-cell side condition never applies; and `n = 2b+1 ≥ 5` for
every `b ≥ 2`. The level differences run `1,…,b` and cell-mates take the value `2`, so
after scaling by `1/b` the values are exactly `1/b, 2/b, …, b/b`, with maximum `1`.

Concrete carrier and metric:

```lean
abbrev BowtieCarrier (b : ℕ) : Type := Unit ⊕ (Fin b × Fin 2)

def bowtieLevel {b : ℕ} : BowtieCarrier b → ℕ
  | Sum.inl _        => 0
  | Sum.inr (i, _)   => (i : ℕ) + 1

noncomputable def bowtieRaw (b : ℕ) (x y : BowtieCarrier b) : ℝ :=
  if bowtieLevel x = bowtieLevel y then (if x = y then 0 else 2)
  else |(bowtieLevel x : ℝ) - (bowtieLevel y : ℝ)|

noncomputable def bowtieScaled (b : ℕ) (x y : BowtieCarrier b) : ℝ :=
  bowtieRaw b x y / b
```

Given `q ∈ (0,1]`, write `q = a/b` with `b ≥ 2` — always possible, doubling numerator and
denominator if the reduced denominator is `1`, which also handles `q = 1` as `2/2` and
removes the need for a separate two-point case. Then `1 ≤ a ≤ b`, and `a/b` is the value of
`bowtieScaled b` on any pair at level difference `a`.

## 2. The rigidity argument, in perturbation form

The companion paper proves extremality of the *ray* via the tight-triple criterion. **Do
not reproduce that.** The whole argument transports into the perturbation vocabulary already
in `Perturbation.lean`, and the last step becomes easier rather than harder.

**Tight triples of `bowtieRaw`.** Exactly the *chains* (`L x < L y < L z` or the reverse)
and the *vees* (`L x = L z`, `x ≠ z`, `L y = L x ± 1`, giving `1 + 1 = 2`). Nothing else.
This catalogue is a finite case analysis on levels and should be an early lemma; the
companion paper's §2 gives the three excluded patterns.

**Step 1 — the four-cycle lemma, perturbation form.** For a four-cycle `x—u—y—v` whose four
sides are edges and whose two diagonals are realized as vees through both remaining points,
the four vee-tightness relations give, with `A = ε x u`, `B = ε u y`, `C = ε x v`,
`D = ε v y`:

```
A + B = C + D        (from the two vees on the diagonal x—y)
A + C = B + D        (from the two vees on the diagonal u—v)
```

Subtracting yields `B = C` and then `A = D`. So `ε u y = ε x v` and `ε x u = ε v y` — the
exact analogue of the companion's `lem:4cycle`, obtained from `pert_add_of_tight` alone.

**Step 2 — uniformity.** All edges of `B_b` carry a common value `λ` of `ε`. Follow the
companion's `lem:uniformity`: disjoint edges within a block, then edges sharing an endpoint,
then across consecutive blocks. With all interior cells of size exactly `2` the case
analysis is smaller than the general statement.

**Step 3 — recovery.** `ε = λ · bowtieRaw` pointwise: cell-mates via a vee (`2λ`), and level
difference `t` by induction on `t` via a chain.

**Step 4 — the finish, which is where the body is easier than the cone.** Any pair at level
difference `b` has `bowtieScaled b = 1`, so `pert_eq_zero_of_dist_eq_one` gives `ε = 0`
there. By Step 3 that value is `λ · b / b = λ`. Hence `λ = 0` and `ε = 0`.

No normalization argument, no `ray-to-point` bridge, no cone. `Rigid (bowtieScaled b)`
falls straight out.

## 3. Traps — both must FAIL

**Trap E — the size hypothesis is not decorative.** The four-point bowtie `B_{2,2}`, whose
graph is `C₄`, is not rigid.

```lean
-- FALSE. Must not be provable.
theorem bowtie22_rigid : Rigid (fun x y => bowtie22 x y / 2)
```

Exhibit the perturbation: with cells `{1,2}`, `{3,4}` and scaled values `1/2` on the four
edges, `1` on the two cell-mate pairs, the assignment `ε₁₃ = ε₂₄ = t`, `ε₁₄ = ε₂₃ = -t`
(and `0` on cell-mate pairs) is a perturbation for `|t| ≤ 1/2` — every triangle inequality
that was tight stays tight, since `(1/2 + t) + (1/2 - t) = 1`. So `C₄` decomposes and the
requirement that interior cells have size at least `2` cannot simply be dropped from the
end cells as well.

**Trap F — the unscaled bowtie is not in `M̄`.** The normalization step is load-bearing and
was one of the two risks flagged in the Tier 4 return.

```lean
-- FALSE. Must not be provable.
theorem bowtieRaw_isBddPseudo (b : ℕ) : IsBddPseudo (bowtieRaw b)
```

For `b ≥ 2` it takes the value `2`, violating `le_one`. One line to refute; it exists so
that no later refactor quietly drops the division by `b`.

## 4. Discharge and restatement

With `exists_finite_rigid_realizing` in hand:

1. Restate as `separable_extends_to_extreme'` and `exists_countable_extreme_realizing'`
   with `hrat` removed, each proved by applying the old form to the new lemma. **Keep the
   hypothesised forms as well** — they document the dependency structure and cost nothing.
2. Add `#print axioms` lines for `exists_finite_rigid_realizing`, both primed theorems, and
   both trap refutations.
3. Update the coverage ledger: Proposition 5.1 moves from `hypothesis (hrat, …)` to
   `formalized (exists_finite_rigid_realizing)`, and the rows for Theorem 1.1 and
   Corollary 1.2 drop the conditionality. Add a line recording that the single-family
   construction of §1 supersedes the companion paper's two-case proof of
   `cor:rational-distances`, since that is a small improvement to the companion and should
   be reported back rather than lost.

## 5. Closure criteria

* `lake build` green; `sorry` grep excluding `.lake/` empty.
* All `#print axioms` lines report only `propext`, `Classical.choice`, `Quot.sound`.
* Both traps reported unproved with counterexamples.
* Coverage ledger showing **every numbered result of the paper formalized, with no
  hypotheses and no omissions**.

## 6. Sizing

One round if the tight-triple catalogue and uniformity go smoothly; two if uniformity
overruns, in which case split at Step 2 and hand back Steps 1 and 3–4 complete. Step 2 is
the only place with real case analysis.
