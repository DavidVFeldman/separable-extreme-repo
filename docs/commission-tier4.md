# Aristotle commission — `separable-extreme`, Tier 4

**Target.** Complete the formalization of *Every Separable Metric Space Extends to an
Extreme One* by constructing the extension and proving Theorem 1.1 and Corollary 1.2.

**Prior art in the tarball.** The Tier 1–3 development
(`RequestProject/{Perturbation,Glue,Subdivide,Traps}.lean`) is ground truth and is not to be
re-proved or modified except as §5 below directs. `rigid_of_chain` is the interface this
tier plugs into.

**Standing caveat.** No Lean here was compiled by the author of this commission. Code blocks
fix statement shapes and names, not working syntax.

---

## 0. Census first

1. **The dependency.** Paper Proposition 5.1 — every rational in `(0,1]` is a distance in a
   finite extreme metric — is *not* in the companion paper's Lean development. That
   development formalizes `thm:bowtie-general` and `thm:ray-to-point` but **not**
   `cor:rational-distances`, which is the result Proposition 5.1 quotes. Confirm this
   against the companion development if it is available in the environment, and report.
2. Does Mathlib have an amalgamated / pushout pseudometric over a family of subspaces? Look
   for path-metric or quotient-metric constructions. We expect not; confirm.
3. `Encodable` / `Denumerable` / `Countable` API for indexing a countable set by `ℕ`, and
   for injecting a countable sum type into `ℕ`.

---

## 1. The architecture — read this before writing anything

The paper's §5 describes a dovetailed recursion over a task list that grows as it is
consumed. **Do not formalize that.** The recursion collapses to exactly two stages, because
the task dependency is only one level deep:

* a *rational* target is discharged by gluing in a finite extreme metric, which creates no
  new targets — the new distances are either `1` or tight through the two-point gluing
  locus;
* an *irrational* target is discharged by subdividing, which creates new targets, but all of
  them are **rational**, hence discharged by the previous bullet.

So: subdivide every irrational target at once, then glue every rational target at once. Two
stages, not a dovetail. The chain handed to `rigid_of_chain` has length three and is
constant thereafter:

```
S 0 = X,   S 1 = X ∪ (all subdivision chains),   S k = univ for k ≥ 2
N 0 = subdivision points,  N 1 = finite-extreme-piece points,  N k = ∅ for k ≥ 2
```

This is the single decision that makes the tier tractable. If it fails, report why before
falling back to a dovetail.

---

## 2. Tier 4a — two lemmas that must come first

### 2.1 Tight chains

`pert_add_of_tight` handles one intermediate point. Stage-1 cross pairs need two, and the
general form costs nothing extra.

```lean
theorem pert_add_of_tight_chain {X : Type*} (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {m : ℕ} (p : ℕ → X)
    (htight : d (p 0) (p m) = ∑ i ∈ Finset.range m, d (p i) (p (i+1))) :
    ε (p 0) (p m) = ∑ i ∈ Finset.range m, ε (p i) (p (i+1))
```

Key observation for the proof: if the total is tight then **every** sub-triple is tight,
because the triangle inequality applied stepwise gives a chain of `≤` whose ends are equal,
so no slack exists anywhere. Induct on `m`, splitting off `p 0, p 1`.

### 2.2 Truncation

```lean
theorem isBddPseudo_min_one {X : Type*} {ω : X → X → ℝ}
    (hnn : ∀ x y, 0 ≤ ω x y) (hdiag : ∀ x, ω x x = 0) (hsymm : ∀ x y, ω x y = ω y x)
    (htri : ∀ x y z, ω x z ≤ ω x y + ω y z) :
    IsBddPseudo (fun x y => min 1 (ω x y))
```

Triangle inequality: if either summand on the right is `≥ 1` the right side is `≥ 1 ≥` the
left; otherwise both are untruncated and the hypothesis applies. This lemma exists so that
§3 can build an unbounded amalgam first and truncate second, rather than carrying the
truncation through a large case analysis as `Glue.lean` does.

---

## 3. Tier 4b — gluing a family

Generalize `Glue.lean` from one piece to an indexed family, all glued along finite loci in a
common base. This is the substantial new Lean work in the tier.

Data: a base `(X, d)`, an index type `I`, and for each `i : I` a finite nonempty
`F i : Finset X`, a type `P i` of new points, and
`ρ i : (P i ⊕ F i) → (P i ⊕ F i) → ℝ` agreeing with `d` on `F i`. Carrier
`Ω := X ⊕ (Σ i, P i)`.

Define the *untruncated* amalgam by the four cases

```
ω (inl x)      (inl x')       = d x x'
ω (inl x)      (inr ⟨i,y⟩)    = min over z ∈ F i of  d x z + ρ i z y
ω (inr ⟨i,y⟩)  (inr ⟨i,y'⟩)   = ρ i y y'                      -- same index
ω (inr ⟨i,y⟩)  (inr ⟨j,y'⟩)   = min over z ∈ F i, z' ∈ F j of ρ i y z + d z z' + ρ j z' y'
```

(all minima over finite nonempty `Finset`s, so attained), then set
`glueFamily := fun a b => min 1 (ω a b)`.

Deliverables:

```lean
theorem glueFamily_isBddPseudo : IsBddPseudo (glueFamily d ρ)
theorem glueFamily_restrict_base : ∀ x x' : X, glueFamily d ρ (inl x) (inl x') = d x x'
theorem glueFamily_restrict_piece (i : I) :
    ∀ y y' : P i ⊕ F i, glueFamily d ρ (embed i y) (embed i y') = ρ i y y'
theorem glueFamily_dichotomy_base_piece (x : X) (i : I) (y : P i) :
    glueFamily d ρ (inl x) (inr ⟨i,y⟩) = 1 ∨
      ∃ z ∈ F i, glueFamily d ρ (inl x) (inr ⟨i,y⟩)
        = glueFamily d ρ (inl x) (inl z) + glueFamily d ρ (inl z) (inr ⟨i,y⟩)
theorem glueFamily_dichotomy_piece_piece {i j : I} (hij : i ≠ j) (y : P i) (y' : P j) :
    glueFamily d ρ (inr ⟨i,y⟩) (inr ⟨j,y'⟩) = 1 ∨
      ∃ z ∈ F i, ∃ z' ∈ F j, (a three-term tight chain through inl z, inl z')
```

`glueFamily_restrict_base` and `_restrict_piece` matter as much as the dichotomies: the
whole argument needs each glued finite extreme piece to sit isometrically inside `Ω`, so
that `pert_eq_zero_on_of_rigid_restrict` applies to it.

**Risk note.** `glueFamily_isBddPseudo` is the one proof in this tier that could overrun.
If the four-case triangle analysis proves unwieldy, the fallback is to define `ω` as the
infimum over finite chains (a path pseudometric, for which the triangle inequality is
immediate) and then prove the explicit formula agrees with it — the dichotomies need the
explicit formula, but the pseudometric property comes free. Report which route was taken.

---

## 4. Tier 4c — the construction and the theorem

With §3 in hand:

1. **Targets.** Fix a countable `A : Set X` with `DenseFor d A`. Let
   `T := {p : A × A | 0 < d p.1 p.2 ∧ d p.1 p.2 < 1}`, countable.
2. **Stage 1.** Index by the irrational targets. For each, `exists_rat_seq_hasSum` gives the
   gaps and the chain `C ≅ ℕ`; glue the family. Verify the hypotheses of
   `pert_eq_tsum_of_geodesic` hold in the amalgam — this is where
   `glueFamily_restrict_piece` is consumed.
3. **Stage 2.** Index by all rational targets: the rational members of `T`, together with
   every gap pair created in stage 1. For each, Proposition 5.1 supplies a finite extreme
   metric realizing that rational; glue the family.
4. **Carrier.** Both stages add countably many points, so `X̃ ≃ X ⊕ ℕ`. Produce the
   bijection explicitly; `Countable`/`Denumerable` should suffice.
5. **Discharge `rigid_of_chain`.** `hbase` from §2's targets plus `pert_eq_zero_of_dense`;
   `hnew` from `pert_eq_zero_on_of_rigid_restrict` on the pieces, `pert_eq_zero_of_gaps_zero`
   on the chains, and `pert_add_of_tight_chain` on piece-to-piece cross pairs; `hcross` from
   `glueFamily_dichotomy_base_piece`.
6. **Conclude.**

```lean
theorem separable_extends_to_extreme {X : Type*} (d : X → X → ℝ) (hd : IsBddPseudo d)
    {A : Set X} (hA : A.Countable) (hAd : DenseFor d A)
    (hrat : ∀ q : ℚ, 0 < q → q ≤ 1 →                          -- Proposition 5.1
      ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
        IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)) :
    ∃ (Ω : Type _) (ι : X → Ω) (d̃ : Ω → Ω → ℝ),
      Function.Injective ι ∧ (Set.range ι)ᶜ.Countable ∧
      IsBddPseudo d̃ ∧ Rigid d̃ ∧ (∀ x y, d̃ (ι x) (ι y) = d x y)
```

**State `hrat` as an explicit hypothesis, exactly as written.** See §5.

---

## 5. The dependency, and why it is a hypothesis for now

Proposition 5.1 is not a standard result from the literature; it is
`cor:rational-distances` of the companion paper, and it is **not currently in the companion
paper's Lean development**, which covers `thm:bowtie-general` and `thm:ray-to-point` but
stops short of the corollary that instantiates them.

So the honest interim shape is an implication, with `hrat` as a hypothesis — which is what
§4 specifies. Two things then close the gap, and **neither is in scope for this
commission**:

* formalize `cor:rational-distances` in the companion development, as an instantiation of
  the already-formalized `thm:bowtie-general` with the cell sizes that produce value set
  `{1/q, …, q/q}`, plus `thm:ray-to-point` to move from cone to body; then
* discharge `hrat` here and restate `separable_extends_to_extreme` without it.

Report whether `cor:rational-distances` looks like a short increment on
`thm:bowtie-general` or a campaign of its own; that estimate decides whether the separable
paper can claim unconditional verification.

Corollary 1.2 of the paper (prescribed countable distance sets) should be derived from
`separable_extends_to_extreme` once available, using the explicit ultrametric of the
paper's proof.

---

## 6. Traps — both must FAIL

**Trap C — two stages are not one.** State and attempt: gluing the finite extreme pieces
*without* first subdividing suffices, i.e. that every target of `T` can be discharged in a
single family gluing.

```lean
-- FALSE. Must not be provable.
theorem one_stage_suffices … : Rigid (glueFamily d ρ) …
```

It fails for any `X` with an irrational distance between two points of `A`: no finite
extreme metric has an irrational distance, since a vertex of a rational polytope is
rational, so no piece can freeze that pair. Exhibit a two-point `X` with
`d x y = 1/√2` and show no `ρ` from `hrat` realizes it.

**Trap D — density is not enough on its own.** State and attempt: if `ε` vanishes on
`A × A` for `A` dense then `d` is rigid, *without* the perturbation hypothesis linking `ε`
to `d`.

```lean
-- FALSE. Must not be provable.
theorem dense_zero_implies_rigid … : (∀ a ∈ A, ∀ b ∈ A, ε a b = 0) → Rigid d
```

`pert_eq_zero_of_dense` needs `IsPerturbation d ε`; the bound `|ε| ≤ d` is what supplies
continuity. A counterexample with `A` dense and an arbitrary `ε` vanishing on `A × A` but
not everywhere is immediate.

---

## 7. Closure criteria

* `lake build` green; `grep -rn "sorry" --include=*.lean . | grep -v '\.lake/'` empty.
* `#print axioms` for `pert_add_of_tight_chain`, `glueFamily_isBddPseudo`,
  `glueFamily_dichotomy_base_piece`, `glueFamily_dichotomy_piece_piece`,
  `separable_extends_to_extreme`, and the Corollary 1.2 statement, all reporting only
  `propext`, `Classical.choice`, `Quot.sound`.
* Both traps reported unproved, with counterexamples.
* An updated `VERIFICATION.md` carrying the **coverage ledger** of §8.

## 8. Coverage ledger — required deliverable

`VERIFICATION.md` must end with a table, one row per numbered result of the paper, with
exactly one of: `formalized`, `hypothesis (name, why)`, `not formalized (why)`. No result
may be omitted. The standing goal for this project is that a paper's verification note
lets a reader see the whole dependency surface at a glance, including what is assumed and
by whom it is discharged.

For this paper the expected final state is: every result `formalized`, except Proposition
5.1, which is `hypothesis (hrat, discharged in the companion development)` until
`cor:rational-distances` lands there.
