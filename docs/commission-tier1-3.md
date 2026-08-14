# Aristotle commission — `separable-extreme`

**Target.** Lean 4 / Mathlib formalization of *Every Separable Metric Space Extends to an
Extreme One* (Feldman–Kehoe), `separable-extreme.tex` in the tarball.

**Ground truth is the tarball.** `separable-extreme.tex` and `separable-extreme.pdf` are the
statements to be formalized; where this commission and the paper disagree, the paper wins
and the discrepancy should be reported rather than silently resolved.

**A warning about the Lean below.** No Lean in this commission has been compiled. There is
no Mathlib in the environment it was written in. Every code block is a *statement shape*,
fixing the intended formalization and the names, not working code. Signatures will need
adjustment against current Mathlib; report any place where the intended statement cannot be
expressed as written.

---

## 0. Census first

Before writing anything, check what already exists:

- Does Mathlib have a development of the space of pseudometrics on a fixed type as a convex
  set? Search `PseudoMetricSpace`, `Set.extremePoints`, `Convex`, and any bundled
  "space of metrics". We expect the answer is no and that `d : X → X → ℝ` with an explicit
  predicate is required, but confirm.
- `Set.extremePoints`, `Convex`, `openSegment` API: what is the current characterization
  lemma linking extreme points to midpoints of segments?
- Summability API: `HasSum`, `tsum`, `Summable.of_nonneg_of_le`, and comparison tests.
- Density of ℚ in ℝ: what is available for producing a strictly increasing rational
  sequence converging to a given positive real?

Report the census before Tier 1.

---

## 1. Conventions

Work with an arbitrary `X : Type*`, no topology or metric instance. A metric is data, not a
typeclass instance, because the whole subject is a convex set of such data.

```lean
variable {X : Type*}

structure IsBddPseudo (d : X → X → ℝ) : Prop where
  nonneg   : ∀ x y, 0 ≤ d x y
  le_one   : ∀ x y, d x y ≤ 1
  diag     : ∀ x, d x x = 0
  symm     : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

def IsPerturbation (d ε : X → X → ℝ) : Prop :=
  (∀ x y, ε x y = ε y x) ∧ (∀ x, ε x x = 0) ∧
  IsBddPseudo (fun x y => d x y + ε x y) ∧
  IsBddPseudo (fun x y => d x y - ε x y)

/-- The paper's working notion of extremality. -/
def Rigid (d : X → X → ℝ) : Prop :=
  ∀ ε, IsPerturbation d ε → ∀ x y, ε x y = 0
```

`nonneg` is redundant (it follows from `triangle`, `diag`, `symm`) but keep it as a field;
deriving it costs a lemma and buys nothing.

Prefer `∀ x y, ε x y = 0` over `ε = 0` throughout, to avoid `funext` friction.

---

## 2. Tier 1 — the convex-geometry bridge

The paper's Proposition 2.2. This tier exists so that the headline theorem is about genuine
extreme points and not merely about a proxy.

```lean
theorem convex_bddPseudo : Convex ℝ {d : X → X → ℝ | IsBddPseudo d}

theorem rigid_iff_extremePoint (d : X → X → ℝ) (hd : IsBddPseudo d) :
    Rigid d ↔ d ∈ ({d : X → X → ℝ | IsBddPseudo d}).extremePoints ℝ
```

Proof notes. Forward: if `d ∈ openSegment ℝ a b` with `a b` in the set, write
`d = t • a + (1-t) • b` with `0 < t < 1` and take `ε = min t (1-t) • (a - b)`; then
`d ± ε = (t ± min t (1-t)) • a + (1 - t ∓ min t (1-t)) • b` is a convex combination of `a`
and `b`, hence in the set by `convex_bddPseudo`. Rigidity forces `ε = 0`, so `a = b`.
Backward: from a nonzero perturbation `ε`, `d` is the midpoint of `d + ε` and `d - ε`,
which are distinct and in the set.

Expect this tier to be short. If Mathlib's `extremePoints` characterization turns out
awkward, report it and proceed with `Rigid` as the working definition for Tiers 2–3; the
bridge can be a later round.

---

## 3. Tier 2 — the four perturbation lemmas

This is the mathematical core and all four are short. **Complete bodies are supplied where
the structure matters.**

### 3.1 The bound (paper Lemma 2.3) — the load-bearing lemma

```lean
theorem abs_pert_le (d ε : X → X → ℝ) (h : IsPerturbation d ε) (x y : X) :
    |ε x y| ≤ min (d x y) (1 - d x y)
```

From `0 ≤ d x y - ε x y` and `0 ≤ d x y + ε x y` get `|ε x y| ≤ d x y`; from
`d x y + ε x y ≤ 1` and `d x y - ε x y ≤ 1` get `|ε x y| ≤ 1 - d x y`. Then `le_min`.

Two corollaries, both used repeatedly:

```lean
theorem pert_eq_zero_of_dist_eq_zero (h : IsPerturbation d ε) (hxy : d x y = 0) : ε x y = 0
theorem pert_eq_zero_of_dist_eq_one  (h : IsPerturbation d ε) (hxy : d x y = 1) : ε x y = 0
```

### 3.2 Tight constraints are preserved (paper Lemma 2.4)

```lean
theorem pert_add_of_tight (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {x y z : X} (htight : d x z = d x y + d y z) :
    ε x z = ε x y + ε y z
```

Apply `triangle` of `d + ε` at `x y z`, subtract `htight`, get `≤`; the same for `d - ε`
gives `≥`; `le_antisymm`.

### 3.3 Restriction (paper Corollary 2.6)

Restriction along `Subtype.val` for `A : Set X`:

```lean
theorem isPerturbation_restrict (d ε : X → X → ℝ) (h : IsPerturbation d ε) (A : Set X) :
    IsPerturbation (fun a b : A => d a b) (fun a b : A => ε a b)

theorem pert_eq_zero_on_of_rigid_restrict (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {A : Set X} (hA : Rigid (fun a b : A => d a b)) :
    ∀ a ∈ A, ∀ b ∈ A, ε a b = 0
```

### 3.4 Density (paper Lemma 2.5) — supply this body

This is the lemma the thesis got wrong, so formalize it exactly as stated. "Dense" must be
phrased without a topology instance, because `d` is one of many metrics on `X`:

```lean
def DenseFor (d : X → X → ℝ) (A : Set X) : Prop :=
  ∀ x : X, ∀ η > 0, ∃ a ∈ A, d x a < η

theorem pert_eq_zero_of_dense (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {A : Set X} (hA : DenseFor d A) (hzero : ∀ a ∈ A, ∀ b ∈ A, ε a b = 0) :
    ∀ x y, ε x y = 0 := by
  intro x y
  -- ρ := d + ε is a bounded-by-1 pseudometric
  -- for a ∈ A: |ρ x y - ρ a b| ≤ ρ x a + ρ b y ≤ 2 * d x a + 2 * d b y   (by abs_pert_le)
  -- and ρ a b = d a b, |d x y - d a b| ≤ d x a + d b y
  -- so |ε x y| = |ρ x y - d x y| ≤ 4 * (d x a + d b y), which is < any η
  sorry
```

The clean route is an `ε`-argument: show `∀ η > 0, |ε x y| ≤ η`, then
`le_of_forall_pos_le_add` or `abs_eq_zero`-style. Given `η > 0`, pick `a b ∈ A` with
`d x a < η/8` and `d y b < η/8`. Then

- `ρ x a ≤ d x a + |ε x a| ≤ 2 * d x a` by `abs_pert_le`,
- `|ρ x y - ρ a b| ≤ ρ x a + ρ b y` by two applications of `triangle` for `ρ`,
- `ρ a b = d a b` since `ε a b = 0`,
- `|d x y - d a b| ≤ d x a + d b y` by two applications of `triangle` for `d`,

and `|ε x y| = |ρ x y - d x y| ≤ |ρ x y - ρ a b| + |d a b - d x y| ≤ 4 * (d x a + d y b) < η`.

The `|p - q| ≤ r + s` steps from two triangle inequalities are the only fiddly part; a
helper lemma `dist_sub_dist_le` for an arbitrary `IsBddPseudo` is worth extracting.

---

## 4. Tier 3 — gluing, subdivision, assembly

### 4.1 Gluing (paper Lemma 3.1)

Model the amalgam concretely to avoid quotient types. Let `P Q : Type*` be the two "new"
parts and `F : Type*` finite and nonempty the intersection; the glued carrier is
`Ω := P ⊕ F ⊕ Q`. Take as input `d : (P ⊕ F) → (P ⊕ F) → ℝ` and
`ρ : (F ⊕ Q) → (F ⊕ Q) → ℝ`, both `IsBddPseudo`, agreeing on `F`. Define `ω` on `Ω` by the
three cases, with the cross case

```lean
noncomputable def glueCross (d ρ) (x : P) (y : Q) : ℝ :=
  min 1 (⨅ z : F, d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y))
```

using `Finset.inf'` over `Finset.univ : Finset F` rather than `iInf`, so that attainment is
definitional. Deliverables:

```lean
theorem glue_isBddPseudo : IsBddPseudo (glue d ρ)
theorem glue_dichotomy (x : P) (y : Q) :
    glue d ρ x y = 1 ∨ ∃ z : F, glue d ρ x y = glue d ρ x z + glue d ρ z y
```

The triangle inequality splits into the paper's three cases (§3, Cases 1–3) plus the two
"all in one side" cases. **This is the longest single proof in the commission**; budget for
it accordingly and consider a helper reducing Case 3 to Case 2 by symmetry rather than
re-proving it.

### 4.2 Subdivision (paper Lemma 4.1)

Two separable pieces.

```lean
theorem exists_rat_seq_hasSum {t : ℝ} (ht : 0 < t) :
    ∃ a : ℕ → ℚ, (∀ i, 0 < a i) ∧ HasSum (fun i => (a i : ℝ)) t
```

Route: pick a strictly increasing rational sequence `q : ℕ → ℚ` with `q 0 = 0` and
`(q j : ℝ) → t`, then `a i = q (i+1) - q i`. Producing `q` is the only place where the
density of ℚ in ℝ is used; check the census for what Mathlib provides before hand-rolling.

```lean
theorem pert_eq_tsum_of_geodesic
    (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    (c : ℕ → X) (y₀ : X) (a : ℕ → ℝ) (t : ℝ)
    (hgap  : ∀ i, d (c i) (c (i+1)) = a i)
    (hpre  : ∀ j, d (c 0) (c j) = ∑ i ∈ Finset.range j, a i)
    (htail : ∀ j, d (c j) y₀ = t - ∑ i ∈ Finset.range j, a i)
    (hsum  : HasSum a t) :
    HasSum (fun i => ε (c i) (c (i+1))) (ε (c 0) y₀)
```

Proof shape: `pert_add_of_tight` on `[c 0, c j, c (j+1)]` gives
`ε (c 0) (c (j+1)) = ε (c 0) (c j) + ε (c j) (c (j+1))`, so the partial sums of
`ε (c i) (c (i+1))` are `ε (c 0) (c j)`. `pert_add_of_tight` on `[c 0, c j, y₀]` gives
`ε (c 0) (c j) + ε (c j) y₀ = ε (c 0) y₀`. `abs_pert_le` gives
`|ε (c j) y₀| ≤ d (c j) y₀ = t - ∑_{i<j} a i → 0`. Conclude by `HasSum` of the partial
sums. Note the statement is in `HasSum` form deliberately — it is stronger than the `tsum`
form and avoids a summability side condition.

The immediate corollary is what the main proof actually consumes:

```lean
theorem pert_eq_zero_of_gaps_zero (…hypotheses as above…)
    (hgaps : ∀ i, ε (c i) (c (i+1)) = 0) : ε (c 0) y₀ = 0
```

### 4.3 Assembly — the inductive skeleton

**This is the design decision that keeps the campaign tractable.** Do not attempt to build
a colimit of metric spaces. State the induction as a property of a *single* metric on a
*fixed* carrier, with the chain given as a monotone family of subsets. The construction
that produces such data is Tier 4 and out of scope here.

```lean
theorem rigid_of_chain
    (d : X → X → ℝ) (hd : IsBddPseudo d)
    (S N : ℕ → Set X)
    (hmono  : Monotone S)
    (hcover : ∀ x : X, ∃ k, x ∈ S k)
    (hstep  : ∀ k, S (k+1) = S k ∪ N k)
    (hbase  : ∀ ε, IsPerturbation d ε → ∀ x ∈ S 0, ∀ y ∈ S 0, ε x y = 0)
    (hnew   : ∀ k, ∀ ε, IsPerturbation d ε → ∀ x ∈ N k, ∀ y ∈ N k, ε x y = 0)
    (hcross : ∀ k, ∀ x ∈ S k, ∀ y ∈ N k,
        d x y = 1 ∨ ∃ z ∈ S k ∩ N k, d x y = d x z + d z y) :
    Rigid d
```

Proof: induct on `k` for the statement `∀ x ∈ S k, ∀ y ∈ S k, ε x y = 0`. The step splits a
pair of `S (k+1) = S k ∪ N k` into three cases — both old (inductive hypothesis), both new
(`hnew`), one of each (`hcross` plus `pert_eq_zero_of_dist_eq_one` or `pert_add_of_tight`,
where both resulting summands are covered by the previous two cases). Then `hcover` and
`hmono` give any pair a common `k`.

This lemma is where the paper's §5 induction lives, stated so that it needs no
construction. It should be the cleanest proof in Tier 3.

---

## 5. Diagnostic traps — both must FAIL

Two statements are included that look like natural strengthenings and are false. A solver
that reports either as proved has broken something real, and the round should be rejected.
**Report explicitly, for each, that it could not be proved and why.**

**Trap A — gluing without the truncation.** The paper's Remark 3.2 turns on the `min 1 (…)`
in the cross formula. State and attempt:

```lean
-- FALSE. Must not be provable.
theorem glue_no_truncation_isBddPseudo :
    IsBddPseudo (fun x y => glueUntruncated d ρ x y)
```

where `glueUntruncated` omits the `min 1`. It fails `le_one`: take `d x z = 1` and
`ρ z y = 1` for the unique `z ∈ F`, giving a cross distance of `2`. A two-point-per-side
counterexample suffices and should be exhibited.

**Trap B — infinite intersection.** `glue_dichotomy` needs `F` finite so the infimum is
attained. State and attempt the version with `F` an arbitrary nonempty type and `iInf`:

```lean
-- FALSE. Must not be provable.
theorem glue_dichotomy_infinite {F : Type*} [Nonempty F] (x : P) (y : Q) :
    glueIInf d ρ x y = 1 ∨ ∃ z : F, glueIInf d ρ x y = glueIInf d ρ x z + glueIInf d ρ z y
```

The infimum need not be attained; a counterexample with `F = ℕ` and
`d x z_n + ρ z_n y = 1/2 + 1/(n+2)` gives cross distance `1/2`, attained at no `z`.

Both traps are cheap to state and diagnostic precisely because the two hypotheses they
attack — truncation, and finiteness of the gluing locus — are exactly what the main proof
consumes.

---

## 6. Closure criteria

- `lake build` green.
- `#print axioms` for `rigid_iff_extremePoint`, `pert_eq_zero_of_dense`,
  `glue_isBddPseudo`, `glue_dichotomy`, `pert_eq_tsum_of_geodesic`, and `rigid_of_chain`
  showing only `propext`, `Classical.choice`, `Quot.sound`.
- `grep -rn "sorry" --include=*.lean . | grep -v '\.lake/'` empty.
- Both traps reported as unproved, with the counterexamples exhibited (as Lean terms if
  cheap, as prose otherwise).
- Every named hole strictly smaller than the theorem it came from.
- CI: `sorry` grep excluding `.lake/`, `sed`-based axiom parse, audit artifacts uploaded.

---

## 7. Out of scope — Tier 4, a separate commission if Tiers 1–3 land

The construction itself: building `X̃`, the chain `S`, and `d̃`, and discharging `hbase`,
`hnew`, `hcross` of `rigid_of_chain`, together with the dovetailed task list and the
input from the companion paper (Proposition 5.1: every rational in `(0,1]` is a distance in
a finite extreme metric).

Design note for whoever takes it: fix the carrier as `X ⊕ ℕ` from the outset, since
`|X̃ \ X| ≤ ℵ₀` is part of the conclusion. That converts "grow the type" into "grow a
subset of a fixed type", which is what `rigid_of_chain` already expects. The dovetailing is
bookkeeping over a countable task list and is the expensive part; the geometry is all in
Tiers 2–3.

Tiers 1–3 constitute a complete verification of the paper's mathematical core — every
lemma, and the induction that combines them. What Tier 4 would add is the recursion. If
Tier 4 is not attempted, say so plainly in the paper's verification note rather than
implying full coverage; the earlier articles in this project have been bitten by exactly
that kind of overclaim.

---

## 8. Sizing

Four rounds, fresh session each, all state in the tarball.

1. Census + Tier 1 + Tier 2 (§3.1–3.3). Short; mostly `linarith` after unfolding.
2. Tier 2 §3.4 (density) alone. Short but analytically fiddly; supply the helper.
3. Tier 3 §4.1 (gluing). The long one. Expect the case analysis to dominate.
4. Tier 3 §4.2–4.3 (subdivision, assembly) + both traps + closure audit.

If round 3 overruns, split the gluing lemma by case rather than weakening the statement.
