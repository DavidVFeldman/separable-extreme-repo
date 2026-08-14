# Aristotle commission — `separable-extreme`, Tier 6: Sections 6–7

**Target.** Formalize the new material of the revised paper: the canonical extension and
its functoriality (§6), the completion lemma, isolation, limits, recovery, and the metric
content of the graph reduction (§7). On completion, the paper's ledger rows marked
*pending* flip to *formalized*; the rows marked as citing Gao–Kechris and Hjorth stay as
they are — see §5, Scope.

**Ground truth.** The tarball: `paper/separable-extreme.tex` (revised, Sections 6–7 are the
targets) and the Tier 1–5 development, which compiles and is not to be modified except by
addition. **Nothing in this commission was compiled by its author**; code blocks are
statement shapes.

---

## 0. Census

1. Binary expansions in Mathlib: is there usable API for `t = ∑ b_k 2^{-k}`? Search
   `Nat.digits`, `Real` binary/`Int.fract`-based digit lemmas. Expect to hand-roll the
   digit function `bit t k := ⌊2^k * t⌋ - 2 * ⌊2^(k-1) * t⌋` and prove
   `HasSum (fun k => bit t k * 2⁻¹^k) t` for `t ∈ (0,1)`; a comparable lemma may exist for
   the `Nat.digits`/geometric-series side. Report.
2. Topology bridge: to speak of isolated points and derived sets, the bare
   `d : X → X → ℝ` must induce a topology. Check whether it is cheaper to (a) build a
   `PseudoMetricSpace` instance from `IsBddPseudo` and use Mathlib's `derivedSet` /
   `AccPt` / `UniformSpace.Completion`, or (b) stay elementary: define
   `IsIsolated d x := ∃ δ > 0, ∀ y, d x y < δ → d x y = 0` and work with sequences, never
   constructing the completion as an object. **We recommend (b) for Tiers 6b–6c** — the
   recovery theorem is stated below in completion-free form — and (a) only if the census
   shows the instance bridge is genuinely short.
3. `Function.Bijective`/`Equiv` API for extending a bijection piecewise over a sigma type.

---

## 1. Statement strategy: eliminate the completion

The paper states recovery in the completion. Formalizing completions of bare metrics is
avoidable, and the avoidance is mathematically faithful: an isometry of completions
restricts to a distance-preserving bijection between the sets of *non-isolated-closure*
points... rather than reconstruct that, observe that everything the reduction needs is
captured on the countable carriers:

> **(R) Recovery, carrier form.** If `Φ : E(A) → E(B)` is a surjective isometry, then
> `Φ` restricts to a surjective isometry `A → B`, provided every point of `A` and of `B`
> has a partner at irrational distance.

This is stronger than what the paper's completion statement needs for the graph reduction,
because for the graph spaces `X_G` the extension `E(X_G)` is already complete-enough: every
Cauchy sequence in `E(X_G)` that does not stabilize converges to a point of `X_G ⊆ E(X_G)`
(the core is uniformly discrete and complete, chains converge to core points, decorations
are isolated). Formally we sidestep even that: the reduction's backward direction needs
only that isometry of the completions implies isometry of the `E`-carriers, and for spaces
all of whose points are either isolated or in the carrier this follows because an isometry
of completions maps isolated points to isolated points and the carrier is dense. **Tier 6d
states the graph equivalence directly between carriers**, plus one lemma
(`carrier_complete`) showing `E(X_G)` has no missing limit points, which closes the loop
with the completion phrasing of the paper. If the completion route via (a) of the census
turns out short, take it instead and say so.

Characterize core points inside `E(A)` without topology:

```lean
/-- x is a chain-limit point: some sequence of decoration points converges to it. -/
def IsCoreLimit (d : Ω → Ω → ℝ) (S : Set Ω) (x : Ω) : Prop :=
  ∀ δ > 0, ∃ y ∈ S, y ≠ x ∧ d x y < δ
```

with `S` the decoration set; the recovery dichotomy becomes: core points are `IsCoreLimit`
for the decoration set (chains accumulate), decoration points are not `IsCoreLimit` for
anything (isolation).

---

## 2. Tier 6a — canonical selectors

```lean
/-- k-th binary digit of t ∈ (0,1). -/
noncomputable def bit (t : ℝ) (k : ℕ) : ℤ := ⌊2^(k+1) * t⌋ - 2 * ⌊2^k * t⌋

theorem bit_mem (t : ℝ) (k : ℕ) : bit t k = 0 ∨ bit t k = 1
theorem hasSum_bits {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasSum (fun k => (bit t k : ℝ) * (2⁻¹)^(k+1)) t
theorem bits_infinite {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (hirr : Irrational t) :
    {k | bit t k = 1}.Infinite
```

`hasSum_bits`: partial sum through `k` is `⌊2^(k+1) t⌋ / 2^(k+1)`, within `2^{-(k+1)}` of
`t`. `bits_infinite`: were the set finite, `t` would be dyadic rational. The canonical gap
sequence is the increasing enumeration of `{k | bit t k = 1}` (via `Nat.nth` or
`Set.Infinite` enumeration API — census); its partial-sum and gap properties then feed the
existing `pert_eq_tsum_of_geodesic` interface unchanged.

For rational selectors nothing new is needed: `b(q)` is `q.den` (`Rat` API), and the
designated pair of `Bowtie.bowtie b` is `(apex b, pt ⟨a-1, _⟩ false)` — any fixed `Bool`;
functoriality maps patterns by the identity so the choice never varies.

## 3. Tier 6b — the canonical extension and functoriality

Concrete carrier, ordered-pair indexed:

```lean
/-- Decoration index: stage-1 chains over ordered irrational pairs; stage-2 bowties over
ordered rational-distance targets (core pairs and adjacent gap pairs of stage-1 chains). -/
-- Chain points: (u, v, j : ℕ).  Bowtie points: (target, p : Bw b \ anchors).
def ECarrier (A : Type*) (d : A → A → ℝ) : Type* := A ⊕ Chains A d ⊕ Bows A d
noncomputable def EDist (A) (d) : ECarrier A d → ECarrier A d → ℝ := …   -- glue formulas
```

Deliverables:

```lean
theorem E_isBddPseudo (hd : IsBddPseudo d) : IsBddPseudo (EDist A d)
theorem E_extends : ∀ a a' : A, EDist A d (inl a) (inl a') = d a a'
theorem E_rigid (hd : IsBddPseudo d) : Rigid (EDist A d)
theorem E_functor {A B} (dA dB) (ψ : A → B)
    (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a') (hinj : Function.Injective ψ) :
    ∃ Ψ : ECarrier A dA → ECarrier B dB,
      Function.Injective Ψ ∧ (∀ a, Ψ (inl a) = inl (ψ a)) ∧
      ∀ x y, EDist B dB (Ψ x) (Ψ y) = EDist A dA x y
theorem E_functor_comp : …   -- Ψ of a composite is the composite of the Ψ's
theorem E_functor_surj : Function.Bijective ψ → Function.Bijective Ψ
```

Advice: `E_rigid` should be proved by **instantiating the Tier 4 machinery, not
re-proving it** — the two-stage family gluing of `GlueFamily`/`Construct` is exactly this
construction with the existential choices replaced by the canonical selectors; the work is
plumbing the canonical data through `exists_subdivision_extension` /
`exists_freezing_extension` shapes, or better, through their underlying lemmas so the
carrier stays the concrete `ECarrier`. If `Construct.lean`'s interfaces prove too
existential to reuse (they return `∃ Ω …`), report that and refactor them into
carrier-explicit versions rather than duplicating proofs; refactoring by addition (new
carrier-explicit lemmas alongside the old) keeps the Tier 1–5 surface intact.

`E_functor` is the theorem of value. Its proof is the paper's: patterns map by the
identity; every distance formula's inputs are matched. The risk is definitional: make
`EDist` case-split cleanly (nine cases as in `Glue.lean`) so `simp` can push `Ψ` through.

## 4. Tier 6c — isolation, limits, recovery (carrier form)

```lean
def Decor (A d) : Set (ECarrier A d) := {x | ¬ ∃ a, x = inl a}

theorem decor_isolated (hd : IsBddPseudo d) :
    ∀ p ∈ Decor A d, ∃ δ > 0, ∀ y, y ≠ p → EDist A d p y ≥ δ
theorem core_is_limit (hd) (hirr : ∀ a : A, ∃ a', Irrational (d a a')) :
    ∀ a : A, ∀ δ > 0, ∃ p ∈ Decor A d, EDist A d (inl a) p < δ ∧ p ≠ inl a
theorem recovery (hdA hdB) (hirrA) (hirrB)
    (Φ : ECarrier A dA → ECarrier B dB) (hbij : Function.Bijective Φ)
    (hiso : ∀ x y, EDist B dB (Φ x) (Φ y) = EDist A dA x y) :
    ∃ φ : A → B, Function.Bijective φ ∧ (∀ a a', dB (φ a) (φ a') = dA a a') ∧
      ∀ a, Φ (inl a) = inl (φ a)
```

`recovery`'s proof: `Φ` preserves the isolation dichotomy (`decor_isolated` +
`core_is_limit` characterize `inl A` as the non-isolated points, on both sides), so `Φ`
maps `inl A` onto `inl B`; restrict.

`decor_isolated` is Lemma 7.3 of the paper, and its δ is explicit per point (min of anchor
distances and within-piece gaps); no compactness, no completion.

## 5. Tier 6d — the graph equivalence, and Scope

```lean
def graphSpace (G : ℕ → ℕ → Prop) [DecidableRel G] : ℕ → ℕ → ℝ :=
  fun m n => if m = n then 0 else if G m n ∨ G n m then (√3)⁻¹ else (√5)⁻¹

theorem graphSpace_isBddPseudo …
theorem graphSpace_iso_iff (G H) :
    (∃ σ : ℕ ≃ ℕ, ∀ m n, (G m n ↔ H (σ m) (σ n))) ↔
    (∃ φ : ℕ ≃ ℕ, ∀ m n, graphSpace H (φ m) (φ n) = graphSpace G m n)
theorem main_equivalence (G H) :
    (graph iso as above) ↔
    ∃ Φ : ECarrier ℕ (graphSpace G) ≃ ECarrier ℕ (graphSpace H),
      ∀ x y, EDist _ _ (Φ x) (Φ y) = EDist _ _ x y
theorem carrier_complete (G) :
    -- every Cauchy sequence in E(graphSpace G) is eventually constant or converges
    -- to a core point already in the carrier
    …
```

`main_equivalence` forward: `graphSpace_iso_iff` + `E_functor_surj`. Backward: `recovery`
(hypotheses: √3, √5 irrational — `Irrational.sqrt`-adjacent lemmas exist; every point has
irrational partners trivially). `carrier_complete` is what licenses the paper's
completion-level statement from the carrier-level one; prove it from `decor_isolated` plus
uniform discreteness of the core plus chain convergence.

**Scope.** The following are *not* to be formalized, and the coverage ledger must say so
rather than leaving blank rows: Borel-ness of the reduction map, `G_δ`-ness of the extreme
class, universality of graph isomorphism among countable-structure isomorphisms, the
Gao–Kechris theorem, and turbulence (Corollary 7.7 and Proposition 7.8 of the paper rest on
these). These cite [GaoKechris03] and [Hjorth00]; descriptive set theory at this level is
not in Mathlib, and pretending otherwise would be the overclaim this project's ledgers
exist to prevent. `main_equivalence` IS the paper's Theorem 7.6 minus the word "Borel".

## 6. Traps — both must FAIL

**Trap G — recovery without the irrationality hypothesis.**

```lean
-- FALSE. Must not be provable.
theorem recovery_no_hyp : (recovery with hirrA, hirrB deleted)
```

Refute: `A = Bool` with `d = 1/2` off-diagonal. All distances rational: no chains; the
extension consists of `A` plus finitely many bowtie points, everything isolated, and
`core_is_limit` fails at both points of `A`. Exhibit an isometry of a two-point
all-rational example... the cleanest refutation of the *dichotomy* is
`¬ core_is_limit` on this example: prove
`∃ A d a, IsBddPseudo d ∧ ¬ (∀ δ > 0, ∃ p ∈ Decor A d, …)` — i.e. the characterization of
the core as the non-isolated points is false without the hypothesis. (A full
`recovery`-shaped counterexample needs an exotic isometry and is not required; refuting the
characterization suffices and should be stated as such.)

**Trap H — functoriality for 1-Lipschitz maps.**

```lean
-- FALSE. Must not be provable.
theorem E_functor_lipschitz : (E_functor with hψ weakened to dB (ψ a) (ψ a') ≤ dA a a')
```

Refute: a map shrinking one irrational distance to a different irrational changes the
canonical gap sequence; no distance-preserving `Ψ` extending `ψ` exists because the chain
pattern lengths differ... the checkable refutation: two-point spaces `dA = 1/√3`,
`dB = 1/√5`, `ψ = id`-on-points is 1-Lipschitz; a `Ψ` as in the conclusion would preserve
the distance from `inl u` to the first chain point, which is the first canonical gap —
`2^{-k}` with different `k` on the two sides. Compute both first gaps and derive the
contradiction numerically (the digits of `1/√3` and `1/√5` differ early; verify which `k`
and hard-code).

## 7. Closure

* `lake build` green; `sorry` grep excluding `.lake/` empty; all new `#print axioms` lines
  reporting only `propext`, `Classical.choice`, `Quot.sound`.
* Both traps reported unproved, with the refutations above proved as negations.
* Updated coverage ledger with the pending rows flipped and the cited-literature rows
  explicit, per §5.
* Report which census route (topology instance vs. elementary) was taken and why.

## 8. Sizing

Four rounds: (1) census + Tier 6a; (2) Tier 6b through `E_rigid` — the plumbing round,
and the one to split if anything overruns; (3) `E_functor` + Tier 6c; (4) Tier 6d + traps
+ ledger. The single largest risk is the reuse-vs-refactor decision in Tier 6b; make it
early and report it.
