# Verification note — *Every Separable Metric Space Extends to an Extreme One*

Formalization of the paper `separable-extreme.tex` (Feldman–Kehoe), Tiers 1–6 of the
commission. Everything below compiles with `lake build`, with no `sorry` and no
non-standard axioms.

Files:

| file | content |
|---|---|
| `RequestProject/Perturbation.lean` | §2: the convex set `M̄(X)`, Proposition 2.2, Lemmas 2.3–2.5, Corollary 2.6 |
| `RequestProject/Glue.lean` | §3: Lemma 3.1 (amalgam and dichotomy) |
| `RequestProject/Subdivide.lean` | §4 subdivision, Lemma 4.1(3), and the §5 induction `rigid_of_chain` |
| `RequestProject/Traps.lean` | the two Tier 1–3 false strengthenings, with counterexamples |
| `RequestProject/Chain.lean` | Tier 4a: `pert_add_of_tight_chain`, `isBddPseudo_min_one` |
| `RequestProject/Transport.lean` | transport of pseudometrics, perturbations and rigidity along maps |
| `RequestProject/GlueFamily.lean` | Tier 4b: the simultaneous gluing of a family of pieces, its axioms, restrictions and dichotomies |
| `RequestProject/Subdivision.lean` | stage 1 of the construction: all targets subdivided into rational gaps |
| `RequestProject/Freeze.lean` | stage 2: a finite rigid piece glued onto every gap pair |
| `RequestProject/Construct.lean` | Tier 4c: Theorem 1.1 (`separable_extends_to_extreme`) and its extreme-point form |
| `RequestProject/Corollary.lean` | Corollary 1.2 (`exists_countable_extreme_realizing`) |
| `RequestProject/TrapsCD.lean` | the two Tier 4 false strengthenings (Traps C and D), with counterexamples |
| `RequestProject/Bowtie.lean` | Tier 5: the bowtie family `B_b`, its rigidity, and Proposition 5.1 (`exists_finite_rigid_realizing`) |
| `RequestProject/TrapsEF.lean` | the two Tier 5 false strengthenings (Traps E and F), with counterexamples |
| `RequestProject/Unconditional.lean` | Tier 5: Theorem 1.1 and Corollary 1.2 without `hrat` |
| `RequestProject/Bits.lean` | Tier 6a: the canonical selectors — binary digits `bit`, the canonical gap sequence `cgap`, the rational selector `ratOf` |
| `RequestProject/GlueTransport.lean` | transport of the family amalgam along a re-indexing, and a uniform-piece constructor for `IsPieceData` |
| `RequestProject/Stage1.lean` | carrier-explicit stage 1: `subDist` on `X ⊕ T × ℕ`, its chain, gap and rigidity-transfer lemmas |
| `RequestProject/Stage2.lean` | carrier-explicit stage 2: `frzDist` on `W ⊕ Decor2`, the bowtie pieces, and the perturbation-transfer lemmas |
| `RequestProject/Canonical.lean` | Tier 6b: `ECarrier`, `EDist`, and `E_isBddPseudo`, `E_extends`, `E_rigid`, `E_extremePoint` |
| `RequestProject/Functor.lean` | Tier 6b: `EMap` and functoriality — `E_functor`, `E_functor_comp`, `E_functor_surj` |
| `RequestProject/LowerBounds.lean` | Tier 6c: lower bounds for the family amalgam and the bowtie, the isolation input |
| `RequestProject/StageIsolation.lean` | Tier 6c: isolation of chain points in stage 1 and of decoration points in stage 2 |
| `RequestProject/Isolation.lean` | Tier 6c: `decor_isolated`, `core_is_limit`, `core_not_EIsolated`, `recovery` |
| `RequestProject/Graph.lean` | Tier 6d: `graphSpace`, `graphSpace_iso_iff`, `main_equivalence`, and the two hypothesis refutations |
| `RequestProject/Complete.lean` | Tier 6d: the completeness ingredients (`graphSpace_core_discrete`, `chain_tendsto_core`, the two Cauchy lemmas) |
| `RequestProject/TrapsGH.lean` | the two Tier 6 false strengthenings (Traps G and H), with counterexamples |
| `RequestProject/Main.lean` | imports and the axiom audit |

## 0. Census

### 0.1 Tier 1–3 census (unchanged)

* **A convex set of pseudometrics.** Mathlib has no development of the space of
  pseudometrics on a fixed type as a convex set. `PseudoMetricSpace` is a typeclass whose
  data is an instance, so it cannot be quantified over as a point of a convex body without
  bundling. Confirmed: an explicit `d : X → X → ℝ` with the predicate `IsBddPseudo` is
  required, exactly as the commission expected.
* **Extreme points.** `Set.extremePoints 𝕜 A = {x | x ∈ A ∧ ∀ x₁ ∈ A, ∀ x₂ ∈ A,
  x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x}`, with `mem_extremePoints` giving both endpoints and
  `mem_extremePoints_iff_forall_segment` the closed-segment form. The `openSegment`
  characterization was used directly and caused no friction; `Convex` on the Pi type
  `X → X → ℝ` works out of the box.
* **Summability.** `HasSum`, `Summable.of_norm_bounded`, `summable_of_sum_range_le`,
  `Summable.hasSum_iff_tendsto_nat`, `HasSum.tendsto_sum_nat` and `squeeze_zero_norm` are
  all available and sufficient.
* **Density of ℚ in ℝ.** `exists_rat_btwn` is available. There is no ready-made "strictly
  increasing rational sequence converging to a given positive real", so it is hand-rolled:
  a rational `r j` is chosen in `(t - t/2^(j+1), t - t/2^(j+2))`, and the summands are the
  consecutive differences.

### 0.2 Tier 4 census (the three questions of §0 of the commission)

1. **The dependency (Proposition 5.1).** The companion paper's Lean development is **not
   present in this environment** — the only sources available here are
   `separable-extreme.tex`, `separable-extreme.pdf` and the Tier 1–3 Lean files — so the
   claim that it formalizes `thm:bowtie-general` and `thm:ray-to-point` but not
   `cor:rational-distances` could not be checked directly. Nothing in the material at hand
   supplies Proposition 5.1, so it is carried here exactly as the commission specifies: as
   the explicit hypothesis `hrat` of `separable_extends_to_extreme` and of
   `exists_countable_extreme_realizing`. See §6 for the requested estimate.
2. **Amalgamated / pushout pseudometrics in Mathlib.** Confirmed absent. There is no
   amalgam, pushout or gluing construction for (pseudo)metric spaces over a common
   subspace, and no general path/quotient pseudometric that could be specialized to one.
   The closest object is `Metric.glueDist` in `Mathlib/Topology/MetricSpace/Gluing.lean`,
   which glues two spaces along maps from a common index type using a shift parameter `ε`;
   it is not the amalgam of the paper (no finite gluing locus over which a minimum is taken,
   no truncation at `1`, and no dichotomy). Both `Glue.lean` and `GlueFamily.lean` therefore
   define the amalgam by hand.
3. **Countability API.** Adequate. `Set.Countable.to_subtype`, `Subtype.countable`,
   `Countable` instances for `Sum`, `Prod` and `Sigma`, `Set.countable_univ_iff`,
   `Set.Countable.union`, `Set.countable_range`, and — for indexing a countable nonempty
   type by `ℕ` — `exists_surjective_nat` (requiring `[Nonempty]` and `[Countable]`) were all
   that was needed. Working with a surjection `ℕ → F` rather than an equivalence avoids the
   finite/infinite case split entirely; rigidity is then transported by
   `Rigid.comp_surjective` (`Transport.lean`).

### 0.3 Tier 5 census

The companion paper's Lean development is **still not present in this environment** — the
tarball contains only `separable-extreme.tex`, `separable-extreme.pdf`, the Tier 1–4 Lean
files and the commission — so `thm:bowtie-general` and `thm:ray-to-point` could not be
transported.  The self-contained route of §2 of the Tier 5 commission was taken instead:
the bowtie is constructed here and its rigidity is proved directly in the perturbation
vocabulary, with no cone, no normalization bridge and no `ray-to-point` step.

### 0.4 Tier 6 census (the three questions of §0 of the Tier 6 commission)

1. **Binary expansions.** Mathlib **does** have the API, contrary to the commission's
   expectation that it would have to be hand-rolled: `Real.digits t b` (in
   `Mathlib/Analysis/Real/OfDigits.lean`) is the `k`-th base-`b` digit of `t`,
   `Real.ofDigitsTerm` the corresponding summand, and
   `Real.hasSum_ofDigitsTerm_digits : 1 < b → t ∈ Set.Ico 0 1 → HasSum (ofDigitsTerm b (digits t b)) t`
   is exactly the summation statement wanted. `RequestProject/Bits.lean` therefore defines
   the commission's `bit t k = ⌊2^(k+1) t⌋ - 2⌊2^k t⌋`, proves `bit_eq_digits`
   (`bit t k = Real.digits t 2 k` for `0 ≤ t`), and gets `hasSum_bits` from the Mathlib
   lemma rather than from a partial-sum estimate. `bits_infinite` (a non-dyadic, in
   particular an irrational, `t` has infinitely many `1`s) is hand-rolled: from a finite
   digit set the `HasSum` collapses to a finite sum of dyadic rationals, contradicting
   irrationality. The increasing enumeration of `{k | bit t k = 1}` is `Nat.nth`, whose
   `Nat.nth_injective`, `Nat.range_nth_of_infinite` and `Nat.nth_mem_of_infinite` are
   exactly what is needed to reindex the sum; `cgap t j = 2^-(gapIdx t j + 1)` is the
   resulting rational gap sequence and `hasSum_cgap` its summation statement, which feeds
   the stage-1 subdivision interface unchanged.
2. **Topology bridge: route (b), elementary.** No `PseudoMetricSpace` instance is built and
   no completion is constructed anywhere in Tier 6. Isolation is stated directly as
   `∃ δ > 0, ∀ y ≠ x, δ ≤ EDist d x y` (`decor_isolated`), which is *stronger* than the
   pseudometric-safe form; the safe form `EIsolated d x` (`∀ y, EDist d x y < δ → EDist d x y = 0`)
   is derived from it as `decor_EIsolated`, and it is the safe form that the recovery
   argument transports along an isometry. Limits are handled with explicit sequences
   (`ECauchy`, `ETendsto` in `Complete.lean`). The reason for (b) is that the instance route
   buys nothing here: the only topological facts used are "isolated" and "is a limit of
   decoration points", both of which are one-line predicates on `EDist`, whereas the
   instance route would additionally require quotienting out the zero-distance relation
   (`EDist` is a pseudometric, and on the graph spaces it genuinely is one only after the
   diagonal is handled) before Mathlib's `AccPt`/`derivedSet`/`UniformSpace.Completion` API
   applied.
3. **Piecewise bijections.** Needed only trivially. `EMap` is defined by a case split on
   the two-stage sum carrier `(A ⊕ Chains A d × ℕ) ⊕ Decor2` and its bijectivity is proved
   componentwise by hand
   (`EMap_injective`, `EMap_surjective`); `Equiv.ofBijective` is the only `Equiv` API used,
   in `main_equivalence`. No sigma-type gluing of equivalences was required.

## 1. What was proved

Tier 1 (`RequestProject/Perturbation.lean`)

* `convex_bddPseudo : Convex ℝ (bddPseudoSet X)`
* `rigid_iff_extremePoint` — Proposition 2.2

Tier 2 (`RequestProject/Perturbation.lean`)

* `abs_pert_le` — Lemma 2.3, with `pert_eq_zero_of_dist_eq_zero`,
  `pert_eq_zero_of_dist_eq_one`
* `pert_add_of_tight` — Lemma 2.4
* `isPerturbation_restrict`, `pert_eq_zero_on_of_rigid_restrict` — Corollary 2.6
* `pert_eq_zero_of_dense` — Lemma 2.5, with the helper
  `IsBddPseudo.abs_sub_le_add : |d x y - d z w| ≤ d x z + d y w`

Tier 3

* `glue_isBddPseudo`, `glue_dichotomy` — Lemma 3.1
* `exists_rat_seq_hasSum`, `pert_eq_tsum_of_geodesic`, `pert_eq_zero_of_gaps_zero` —
  Lemma 4.1
* `rigid_of_chain` — the §5 induction

Tier 4a (`RequestProject/Chain.lean`)

* `pert_add_of_tight_chain` — a perturbation is additive along a tight chain of any finite
  length, via `IsBddPseudo.tight_of_tight3` (a tight total forces every sub-triple tight)
* `isBddPseudo_min_one` — truncation at `1` of an unbounded pseudometric
* `IsPerturbation.isBddPseudo`, `IsBddPseudo.le_sum_range` (auxiliary)

Tier 4 transport (`RequestProject/Transport.lean`)

* `IsBddPseudo.comp`, `IsPerturbation.comp` — pull back along an arbitrary map
* `Rigid.comp_surjective` — rigidity passes to a surjective re-indexing
* `pert_eq_zero_of_isometry`

Tier 4b (`RequestProject/GlueFamily.lean`)

* `IsPieceData` — the data of a family of finite pieces glued onto a common base
* `glueFamily`, and `glueFamily_isBddPseudo` — the family amalgam is a bounded-by-one
  pseudometric
* `glueFamily_restrict_base`, `glueFamily_restrict_piece`, `glueFamily_restrict_locus` —
  base and pieces sit isometrically inside the amalgam
* `glueFamily_dichotomy_base_piece`, `glueFamily_dichotomy_piece_piece` — each new distance
  is either `1` or tight through the gluing locus

Tier 4c (`RequestProject/Subdivision.lean`, `Freeze.lean`, `Construct.lean`, `Corollary.lean`)

* `exists_subdivision_extension` — stage 1: every target pair is simultaneously subdivided
  into a countable geodesic chain of rational gaps, with the sum formula available and with
  the statement that a perturbation vanishing on all gaps and on the base vanishes
  identically
* `exists_freezing_extension` — stage 2: a finite rigid piece realizing the gap length is
  glued onto every gap pair, freezing every gap
* `separable_extends_to_extreme` — **Theorem 1.1**, in exactly the shape commissioned, with
  `hrat` as an explicit hypothesis
* `separable_extends_to_extremePoint` — Theorem 1.1 in extreme-point form, together with
  separability of the extension
* `prescribedUltrametric`, `prescribedUltrametric_isBddPseudo`,
  `exists_countable_extreme_realizing` — **Corollary 1.2**

Tier 5 (`RequestProject/Bowtie.lean`, `Unconditional.lean`)

* `Bowtie.bowtie` — the normalized bowtie `B_b = B_{1,2,2,…,2}`: one point at level `0`
  (the apex) and two points at each of the levels `1,…,b`, with raw distance `|i-j|`
  between levels `i ≠ j` and `2` between distinct points of a level, all divided by `b`
* `Bowtie.bowtie_isBddPseudo` — `B_b ∈ M̄` for `b ≥ 2`
* `Bowtie.bowtie_chain`, `Bowtie.bowtie_vee` — the tight triples of the bowtie: the chains
  (three strictly increasing levels) and the vees (two distinct points of one level seen
  from a point of an adjacent level)
* `Bowtie.pert_cross`, `Bowtie.pert_vee_down`, `Bowtie.pert_vee_up`, `Bowtie.pert_top`,
  `Bowtie.pert_pair`, `Bowtie.pert_linear` — the steps of the rigidity argument: a
  perturbation is determined across levels by its values against the apex, those values
  depend only on the level, they are linear in the level, and they vanish at the top level
  because the apex and level `b` are at distance exactly `1`
* `Bowtie.bowtie_rigid` — **rigidity of `B_b`** for `b ≥ 2`
* `exists_finite_rigid_realizing` — **Paper Proposition 5.1**, formerly the hypothesis
  `hrat`
* `separable_extends_to_extreme'`, `separable_extends_to_extremePoint'`,
  `exists_countable_extreme_realizing'` — **Theorem 1.1 and Corollary 1.2 without any
  hypothesis beyond their own**

Tier 6a (`RequestProject/Bits.lean`)

* `bit`, `bit_mem`, `bit_eq_digits` — the commission's digit function, identified with
  Mathlib's `Real.digits _ 2`
* `hasSum_bits` — `HasSum (fun k => bit t k * (2⁻¹)^(k+1)) t` for `t ∈ [0,1)`
* `bits_infinite` — an irrational `t ∈ (0,1)` has infinitely many binary `1`s
* `gapIdx`, `cgap`, `cgap_pos`, `cgap_le_one`, `hasSum_cgap` — **the canonical gap
  sequence** of an irrational `t ∈ (0,1)`: positive rationals summing to `t`, chosen by a
  formula, with no arbitrary choice anywhere
* `ratOf`, `ratOf_spec`, `ratOf_cast` — the canonical rational selector

Carrier-explicit refactoring of the Tier 4 stages (`GlueTransport.lean`, `Stage1.lean`,
`Stage2.lean`)

* `Stage1.subDist` on `X ⊕ T × ℕ` with `subDist_isBddPseudo`, `subDist_locus`,
  `subDist_piece`, `subDist_chain`, `subDist_gap`, `subDist_pre`, `subDist_tail`,
  `subDist_rigid_transfer` — stage 1 with the carrier and the chain data in the open,
  rather than behind the `∃ Ω` of `exists_subdivision_extension`
* `Stage2.frzDist` on `W ⊕ Decor2` with `qOf`, `bsz`, `alv`, `pieceDist`, `pieceAnc`,
  `emb_iso`, `frzDist_isBddPseudo`, `frzDist_locus`, `frzDist_piece`, `frz_pert_transfer`
  — likewise for stage 2
* `glueFamily_transport`, `gfBasePiece_transport`, `gfPiecePiece_transport`,
  `isPieceData_of_uniform` — the amalgam under a re-indexing of the pieces, which is what
  makes functoriality provable at the level of the stages

Tier 6b (`RequestProject/Canonical.lean`, `Functor.lean`)

* `Chains`, `RatPairs`, `Bows`, `W1`, `dist1`, `banc`, `ECarrier`, `EDist`, `einl`, `ew1`
  — **the canonical extension** `E(A)`: `Chains A d` is the set of *ordered pairs at
  irrational distance*, `Bows A d` the *ordered rational-distance targets* (core pairs and
  adjacent gap pairs of the chains), and everything — which pairs get chains, which gaps,
  which bowtie, which anchor — is determined by `d` alone: no witness is chosen. (The one
  use of choice, inside `ratOf`, picks the rational a non-irrational real is the cast of,
  and that rational is unique, so the value does not depend on the choice function.)
* `E_isBddPseudo` — `E(A) ∈ M̄`
* `E_extends` — the core embedding `einl` is isometric (it holds by `rfl`)
* `E_rigid`, `E_extremePoint` — **`E(A)` is extreme**, proved by instantiating the two
  carrier-explicit stages and the §5 chain induction, not by re-proving them
* `EMap`, `EMap_einl`, `EMap_iso`, `EMap_injective`, `EMap_surjective`, `EMap_comp`,
  `EMap_id`, `EMap_congr` — the canonical map on extensions induced by an isometric
  injection of cores
* `E_functor`, `E_functor_comp`, `E_functor_surj` — **Theorem `thm:functor`** in the three
  shapes of the commission

Tier 6c (`RequestProject/LowerBounds.lean`, `StageIsolation.lean`, `Isolation.lean`)

* `le_gfBasePiece`, `le_gfPiecePiece`, `glueFamily_piece_isolated`,
  `glueFamily_base_isolated` — lower bounds for the family amalgam: a new distance is at
  least `c` as soon as every cross route is
* `Bowtie.one_le_raw_of_ne`, `Bowtie.inv_le_bowtie`, `Bowtie.bowtie_zero_or_inv_le` — the
  bowtie is `1/b`-uniformly discrete
* `Stage1.cdel`, `subDist_chain_isolated` — the isolation radius of a stage-1 chain point
* `Stage2.frzDist_decor_isolated` — the isolation radius of a stage-2 decoration point
* `Decor`, `EIsolated`, `invb`, `chainDelta`
* `decor_isolated` — **Lemma `lem:isolation`**, in the strong literal form
  `∀ x ∈ Decor A d, ∃ δ > 0, ∀ y ≠ x, δ ≤ EDist d x y`, with `δ` explicit; and
  `decor_EIsolated`, its pseudometric-safe consequence
* `core_is_limit` — **Lemma `lem:limits`**: every core point is a limit of decoration
  points, given a partner at irrational distance; `core_not_EIsolated` is the contrapositive
  form used in recovery
* `recovery` — **Theorem `thm:recovery`, carrier form**: a surjective isometry
  `E(A) → E(B)` restricts to a distance-preserving bijection `A → B`

Tier 6d (`RequestProject/Graph.lean`, `Complete.lean`)

* `graphSpace G m n = 0 / (√3)⁻¹ / (√5)⁻¹` according as `m = n`, `m` and `n` adjacent, `m`
  and `n` non-adjacent, with
  `graphSpace_isBddPseudo`, `graphSpace_irrational`, `graphSpace_hirr` and the numeric
  lemmas `sqrt3_inv_lt`, `lt_sqrt3_inv`, `sqrt5_inv_lt`, `lt_sqrt5_inv`,
  `sqrt3_inv_irrational`, `sqrt5_inv_irrational`, `sqrt3_inv_ne_sqrt5_inv`
* `graphSpace_iso_iff` — isomorphism of simple graphs is isometry of their graph spaces
* `main_equivalence` — **the paper's Theorem `thm:gi` minus the word "Borel"**: two simple
  graphs are isomorphic iff the canonical extensions of their graph spaces — extreme points
  of `M̄`, by `E_rigid` — are isometric
* `graphSpace_iso_iff_needs_symmetry`, `graphSpace_iso_iff_needs_irreflexive` — proofs that
  neither added hypothesis can be dropped (see §2.4)
* `ECauchy`, `ETendsto`, `graphSpace_core_discrete`, `chain_tendsto_core`,
  `cauchy_tendsto_of_recurrent`, `cauchy_eventually_constant_of_decor` — the ingredients of
  `carrier_complete`, which is itself **not formalized** (see §2.4)

## 2. Discrepancies with the commission

All are adjustments of signatures or of the route taken; no mathematical statement of the
paper was weakened.

### 2.1 Tier 1–3 (unchanged)

1. **`glue_isBddPseudo` needs hypotheses.** The commission's shape lists no hypotheses. As
   stated it is false: the amalgam is a bounded-by-one pseudometric only when both inputs
   are and they agree on the gluing locus. The theorem is proved in a section with
   `(hd : IsBddPseudo d)`, `(hr : IsBddPseudo ρ)` and
   `(hFF : ∀ z z' : F, d (Sum.inr z) (Sum.inr z') = ρ (Sum.inl z) (Sum.inl z'))`, which is
   the paper's `d|_{F×F} = ρ|_{F×F}`.
2. **`glue_dichotomy` needs no hypotheses at all**, since it is a statement about the
   truncated finite minimum only. It is stated and proved unconditionally.
3. **`rigid_of_chain` does not need `hd : IsBddPseudo d`.** Every step of the induction goes
   through the perturbation `ε` alone, so the hypothesis was dropped rather than carried
   unused.
4. **Cross distance.** As instructed, `glueCross` uses `Finset.inf'` over
   `Finset.univ : Finset F` (requiring `[Fintype F] [Nonempty F]`), so attainment is
   available without a completeness argument. The glued carrier is the concrete `P ⊕ F ⊕ Q`.
5. The redundant `nonneg` field of `IsBddPseudo` was kept, as instructed, and
   `∀ x y, ε x y = 0` was used throughout in place of `ε = 0`.

### 2.2 Tier 4

6. **Piece data is uniform, not dependent.** The commission's shape has `F i : Finset X`, a
   type `P i` of new points per index, and carrier `X ⊕ (Σ i, P i)`. Formalizing that
   directly forces dependent casts between `P i ⊕ F i` for varying `i` at every step of the
   triangle analysis. Instead `IsPieceData` packages the same information *uniformly*: a
   single type `Y` of new points with an index map `idx : Y → I`, a single finite nonempty
   locus type `L` with maps `g : I → L → X` naming the gluing locus of each piece, a piece
   metric `r : Y → Y → ℝ` and a piece-to-locus distance `s : Y → L → ℝ`, subject to the
   compatibility conditions. Every piece of the construction has the *same* locus size
   (`L = Bool`: exactly two points are glued in), so no generality is lost, and the carrier
   is the plain sum `X ⊕ Y`. The deliverables `glueFamily_isBddPseudo`,
   `glueFamily_restrict_base`, `glueFamily_restrict_piece` and the two dichotomies are
   stated and proved in this formulation.
7. **Which route for `glueFamily_isBddPseudo`.** The **explicit four-case triangle
   analysis** was carried out; the path-metric fallback of the commission's risk note was
   *not* needed. `isBddPseudo_min_one` is what makes this manageable: the amalgam is built
   untruncated and truncated afterwards, so the case analysis never has to interleave with
   the truncation.
8. **One subdivision stage for all targets, not just the irrational ones.** The commission
   splits stage 1 over irrational targets and stage 2 over "the rational members of `T`,
   together with every gap pair created in stage 1". Since *every* positive real — rational
   or not — is a sum of positive rationals, the split is unnecessary:
   `exists_subdivision_extension` subdivides every target, and stage 2 then has a single
   uniform job, namely freezing the gaps. This removes a rationality decision on real
   numbers (which would have needed `Classical` case analysis on `Irrational`) and shortens
   the assembly appreciably. The two-stage architecture of §1 of the commission is otherwise
   exactly what was implemented; no dovetail was needed.
9. **The chain fed to `rigid_of_chain` is used degenerately.** The chain is
   `S 0 = range ι`, `S 1 = range Sum.inl` (base plus subdivision points), `S k = univ` for
   `k ≥ 2`, with `N 0 = range Sum.inl` and `N k = univ` thereafter, as the commission
   prescribes. But the `hcross` obligation is discharged with `z := w` (the trivial
   degenerate triangle `d w w' = d w w + d w w'`), because `hnew` already gives the
   vanishing of the perturbation on all of `N k`: the freezing lemma
   `exists_freezing_extension` returns, as part of its conclusion, the implication
   "a perturbation vanishing on the whole base vanishes everywhere", and
   `exists_subdivision_extension` returns the analogous implication for the subdivision
   points; the proofs of those two implications are where the two dichotomies of
   `glueFamily` are actually consumed. So the §5 induction is genuinely discharged and the
   theorem genuinely proved, but the dichotomy work happens one level down, inside stages 1
   and 2, rather than in `hcross`. A reader tracing the paper's §5 should look at
   `exists_subdivision_extension` and `exists_freezing_extension` for the dichotomy
   arguments.
10. **`separable_extends_to_extreme` is stated with `universe u`** and returns
    `∃ Ω : Type u`, rather than `Type _`; the carrier produced is
    `(X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ`, which lives in the same universe as `X`. The commission's
    `Type _` shape is what this elaborates to.
11. **Corollary 1.2 also carries `hrat`**, since it is derived from Theorem 1.1; the
    prescribed value set is realized by `prescribedUltrametric V`, the paper's ultrametric
    `d(p_*, p_v) = v`, `d(p_v, p_w) = max{v, w}`.

### 2.3 Tier 5

12. **One family, not two cases.** The paper's proof of Proposition 5.1 splits into `q = 1`
    (the two-point partition metric) and `q = a/b` with `0 < a < b` (the generalized
    bowtie), and the companion paper's `cor:rational-distances` splits the latter again into
    `q = 2/b` and `q ≥ 3/b`.  Here a *single* family `B_b = B_{1,2,…,2}` covers every case:
    writing `q = (2·num)/(2·den)` always gives a representation `a/b` with `b ≥ 2` and
    `1 ≤ a ≤ b`, so `q = 1` is `2/2` and needs no separate treatment.  This is a small
    improvement to the companion paper's argument and is reported back as such.
13. **The rigidity proof is elementary and self-contained.** No extreme ray of the metric
    cone, no normalization bridge and no `ray-to-point` theorem appear: the tight triples of
    `B_b` are catalogued directly (`bowtie_chain`, `bowtie_vee`), and `pert_add_of_tight`
    (Lemma 2.4) together with `pert_eq_zero_of_dist_eq_one` (Lemma 2.3) is all the input
    needed.  The four-cycle lemma of the commission's Step 1 is not stated separately: the
    two vee relations at a level are compared directly, which is what the four-cycle lemma
    is used for.
14. **`slope` is a total function.** The commission's `λ` is the common value of a
    perturbation on the edges; here it is `Bowtie.slope ε`, defined as the value against the
    apex at level `1` (with junk value `0` for `b = 0` so that the definition is total).
    `Bowtie.pert_linear` is the statement that a perturbation's value against the apex at
    level `n` is `n · λ`, which is the commission's Steps 2 and 3 combined.

### 2.4 Tier 6

15. **Reuse, not duplication — but by refactoring the stages.** The commission's largest
    flagged risk was the reuse-vs-refactor decision for `E_rigid`. The Tier 4 interfaces
    `exists_subdivision_extension` and `exists_freezing_extension` return `∃ Ω, …`, so their
    carriers cannot be identified with the canonical `ECarrier`. As the commission
    anticipates, they were **refactored by addition**: `Stage1.lean` and `Stage2.lean` state
    the same mathematics with the carrier explicit (`X ⊕ T × ℕ` and `W ⊕ Decor2`), and the
    Tier 4 existential lemmas are left exactly as they were. `E_rigid` is then an
    instantiation. No proof of Tiers 1–5 was modified.
16. **The carrier is a two-stage sum, not a three-way one.** The commission suggests
    `ECarrier = A ⊕ Chains ⊕ Bows`. The construction is two-stage, and stage 2 glues onto
    the *stage-1* space (its targets include the gap pairs created in stage 1), so the
    carrier that makes the stages compose is `(A ⊕ Chains A d × ℕ) ⊕ Decor2`, i.e.
    `W1 A d ⊕ Decor2`. The decoration points are `Decor A d = {x | ¬ ∃ a, x = einl d a}`,
    which is the same set the commission describes.
17. **`decor_isolated` is proved in the strong form.** The commission asks for
    `∃ δ > 0, ∀ y ≠ p, EDist p y ≥ δ`. On a genuine pseudometric that form can fail (two
    distinct points at distance `0`), so a weaker "safe" form was expected to be needed. It
    is not: `EDist` separates the decoration points from everything else, and the literal
    strong statement is what is proved. `decor_EIsolated` derives the safe form, and it is
    the safe form that transports along an isometry in `recovery`.
18. **`graphSpace_iso_iff` and `main_equivalence` need `G` and `H` to be simple graphs.**
    The commission states both for arbitrary relations `G H : ℕ → ℕ → Prop`. In that
    generality the forward direction of `graphSpace_iso_iff` is fine but the backward
    direction is **false**, because `graphSpace` only sees the symmetrized, loop-free part
    of the relation. Both statements therefore carry `Symmetric G`, `∀ n, ¬ G n n`,
    `Symmetric H`, `∀ n, ¬ H n n` — which is what "countable graph" means in the paper —
    and both omissions are refuted, not merely asserted:
    * `graphSpace_iso_iff_needs_symmetry`: `G = {(0,1)}` and `H = {(0,1), (1,0)}` have equal
      graph spaces but are not isomorphic as relations.
    * `graphSpace_iso_iff_needs_irreflexive`: `G = {(0,0)}` and `H = ∅` have equal graph
      spaces but are not isomorphic as relations.
19. **`graphSpace` is classical, not `[DecidableRel G]`.** The commission's shape carries a
    `[DecidableRel G]` instance so the `if`s compute. Carrying it would force the instance
    through every downstream statement (and through `ECarrier ... (graphSpace G)`), and the
    two refutations above would have to supply instances for their ad-hoc relations.
    `graphSpace` is instead defined with `open Classical in` and is `noncomputable`; nothing
    in the development evaluates it.
20. **`carrier_complete` is not formalized.** What is formalized are its ingredients —
    `graphSpace_core_discrete` (the core is `1/√5`-uniformly discrete),
    `chain_tendsto_core` (each canonical chain converges to its terminal core point, so
    chain limits are already in the carrier), `cauchy_eventually_constant_of_decor` (a
    Cauchy sequence meeting a decoration point infinitely often is eventually constant) and
    `cauchy_tendsto_of_recurrent`. The missing case is a Cauchy sequence meeting every point
    only finitely often; settling it means following the sequence down through both stages
    (bowtie points to their anchors, chain points to theirs), showing the anchors are
    themselves Cauchy and eventually lie in one chain. This is recorded as *not formalized*
    in the ledger of §7. Nothing else depends on it: `main_equivalence` is stated and proved
    at carrier level, where `carrier_complete` is not needed.
21. **`lem:completion` is not formalized.** Extremality passing to completions is the one
    numbered result of the paper that is not formalized, and deliberately so: route (b) of
    the census means no completion is ever constructed. Its proof in the paper is two lines
    from `cor:restrict` and `lem:dense`, both of which *are* formalized
    (`isPerturbation_restrict`, `pert_eq_zero_of_dense`); what is missing is only the
    completion object and the density of `X` in it.
22. **Trap H is refuted more cheaply than the commission plans.** The commission suggests
    computing the first canonical gaps of `1/√3` and `1/√5` and hard-coding the differing
    exponent. That is unnecessary: for the weakened (`1`-Lipschitz) hypothesis, the
    conclusion's `∀ x y, EDist dB (Ψ x) (Ψ y) = EDist dA x y` together with
    `Ψ (einl a) = einl (ψ a)` already forces `1/√5 = 1/√3` on the core. The contradiction
    is visible before any chain point is reached.

## 3. The traps — all eight unproved, as required

None of the eight trap statements is proved. Each is recorded as a commented-out statement
together with a Lean counterexample refuting it.

Tier 1–3 (`RequestProject/Traps.lean`):

* **Trap A (gluing without the truncation).** `glue_no_truncation_not_isBddPseudo` proves
  `¬ IsBddPseudo (glueUntruncated trapAmetric trapAmetric)` for `P = F = Q = Unit` with the
  discrete `0/1` metric on `Unit ⊕ Unit` on both sides. Both inputs are bounded-by-one
  pseudometrics and they agree on the gluing locus, yet the untruncated cross distance is
  `d(x,z) + ρ(z,y) = 1 + 1 = 2`, so `le_one` fails.
* **Trap B (infinite gluing locus).** `glue_dichotomy_infinite_false` proves the negation of
  the dichotomy for `F = ℕ`, `P = Q = Unit`, with both inputs pullbacks of the metric of
  `ℝ`: the cross sums are `1/2 + 2/(n+2)`, the infimum `1/2` is not attained, and the cross
  distance is neither `1` nor `ω(x,z) + ω(z,y)` for any `z`.

Tier 4 (`RequestProject/TrapsCD.lean`):

* **Trap C (two stages are not one).** The claim is that every target can be discharged by a
  single family gluing, with no subdivision. The pieces available are exactly those produced
  by the hypothesis `hrat`, and the pair each freezes is at a **rational** distance `(q : ℝ)`
  — so a target at an irrational distance cannot be matched by any piece and the single
  gluing cannot even be set up. `trapC_no_piece_realizes` proves, for the two-point space
  `boolMetric sqrtHalf` with `sqrtHalf = √2/2 ∈ (0,1)` (`trapC_isBddPseudo`,
  `sqrtHalf_pos`, `sqrtHalf_lt_one`), that `(q : ℝ) ≠ boolMetric sqrtHalf false true` for
  every rational `q`, via `sqrtHalf_irrational`. (The stronger geometric fact — no finite
  extreme metric has an irrational distance, a vertex of a rational polytope being rational
  — is the paper's reason; only the consequence actually used is formalized.)
* **Trap D (density is not enough on its own).** The claim is `pert_eq_zero_of_dense` with
  the hypothesis `IsPerturbation d ε` deleted; that hypothesis is what supplies `|ε| ≤ d`
  and hence continuity of `ε`. Both readings are refuted:
  * `trapD_dense_zero_not_rigid` — on the two-point space at distance `1/2`, the whole space
    is dense and the zero map vanishes on it, yet the metric is not rigid:
    `trapD_isPerturbation` exhibits `boolMetric (1/4)` as a nonzero perturbation
    (`d ± ε = boolMetric (3/4)`, `boolMetric (1/4)`).
  * `trapD_dense_zero_not_zero` — on the two-point space carrying the zero pseudometric the
    singleton `{false}` is dense and `boolMetric 1` vanishes on it, yet is not identically
    zero. It is of course not a perturbation of the zero pseudometric.

Tier 5 (`RequestProject/TrapsEF.lean`):

* **Trap E (the size hypothesis is not decorative).** The claim is that the four-point
  bowtie `B_{2,2}`, whose graph is the four-cycle `C₄`, is rigid.
  `TrapE.trapE_bowtie22_not_rigid` refutes it: on the carrier `Bool × Bool` (first
  coordinate the cell, second the point inside it) with `TrapE.d22` the normalized `B_{2,2}`
  (`1` inside a cell, `1/2` across), `TrapE.eps22` — `+1/2` on the two pairs with equal
  second coordinate, `-1/2` on the other two, `0` inside cells — is a perturbation
  (`TrapE.eps22_isPerturbation`) and is nonzero (`TrapE.eps22_ne_zero`).  Every tight
  triangle stays tight because `(1/2 + t) + (1/2 - t) = 1`.  So the first cell of `B_b` must
  be a single point.
* **Trap F (the unscaled bowtie is not in `M̄`).** `trapF_bowtieRaw_not_isBddPseudo` proves
  `¬ IsBddPseudo (Bowtie.raw b)` for every `b ≥ 2`: the two points of level `1` are at raw
  distance `2 > 1`, so `le_one` fails and the division by `b` in `Bowtie.bowtie` cannot be
  dropped.

Tier 6 (`RequestProject/TrapsGH.lean`):

* **Trap G (recovery without the irrationality hypothesis).** The claim is `recovery` with
  `hirrA` and `hirrB` deleted. What those hypotheses buy is the dichotomy "core points are
  exactly the non-isolated points", and it is that dichotomy which fails without them.
  `core_is_limit_needs_irrational` proves
  `∃ A d a, IsBddPseudo d ∧ EIsolated d (einl d a)`: for the two-point space `dhalf` at
  distance `1/2` (`dhalf_isBddPseudo`) every distance is rational (`dhalf_not_irrational`),
  so there are no chains at all (`dhalf_no_chains`), every bowtie glued in has size `2`
  (`dhalf_bsz`), and the core point `false` is at distance at least `1/4` from every other
  point of the extension (`dhalf_core_isolated`). So `core_is_limit` fails at both core
  points and the characterization the recovery proof runs on is unavailable. As the
  commission allows, this refutes the *characterization* rather than exhibiting an exotic
  isometry, and is stated as such.
* **Trap H (functoriality for `1`-Lipschitz maps).** The claim is `E_functor` with `hψ`
  weakened to `dB (ψ a) (ψ a') ≤ dA a a'`. `E_functor_lipschitz_false` refutes it: take
  `dA` the graph space of the complete graph on `ℕ` (all distinct distances `1/√3`), `dB`
  that of the empty graph (all distinct distances `1/√5`) and `ψ = id`, which is
  `1`-Lipschitz since `1/√5 < 1/√3`. A `Ψ` as in the conclusion satisfies
  `EDist dB (Ψ (einl 0)) (Ψ (einl 1)) = EDist dA (einl 0) (einl 1)`, i.e.
  `1/√5 = 1/√3`, contradicting `sqrt3_inv_ne_sqrt5_inv`.

## 4. Audit

`#print axioms` (run in `RequestProject/Main.lean`) reports
`[propext, Classical.choice, Quot.sound]` for every audited declaration:
`rigid_iff_extremePoint`, `pert_eq_zero_of_dense`, `glue_isBddPseudo`, `glue_dichotomy`,
`pert_eq_tsum_of_geodesic`, `rigid_of_chain`, `glue_no_truncation_not_isBddPseudo`,
`glue_dichotomy_infinite_false`, `pert_add_of_tight_chain`, `isBddPseudo_min_one`,
`glueFamily_isBddPseudo`, `glueFamily_restrict_base`, `glueFamily_restrict_piece`,
`glueFamily_dichotomy_base_piece`, `glueFamily_dichotomy_piece_piece`,
`exists_subdivision_extension`, `exists_freezing_extension`,
`separable_extends_to_extreme`, `separable_extends_to_extremePoint`,
`exists_countable_extreme_realizing`, `trapC_no_piece_realizes`,
`trapD_dense_zero_not_rigid`, `trapD_dense_zero_not_zero`, and — for Tier 5 —
`exists_finite_rigid_realizing`, `Bowtie.bowtie_isBddPseudo`, `Bowtie.bowtie_rigid`,
`separable_extends_to_extreme'`, `separable_extends_to_extremePoint'`,
`exists_countable_extreme_realizing'`, `TrapE.trapE_bowtie22_not_rigid`,
`trapF_bowtieRaw_not_isBddPseudo`; and — for Tier 6 — `Canonical.bit_mem`,
`Canonical.hasSum_bits`, `Canonical.bits_infinite`, `Canonical.hasSum_cgap`,
`Canonical.ratOf_spec`, `Canonical.E_isBddPseudo`, `Canonical.E_extends`,
`Canonical.E_rigid`, `Canonical.E_extremePoint`, `Canonical.E_functor`,
`Canonical.E_functor_comp`, `Canonical.E_functor_surj`, `Canonical.decor_isolated`,
`Canonical.core_is_limit`, `Canonical.recovery`, `Canonical.graphSpace_isBddPseudo`,
`Canonical.graphSpace_iso_iff`, `Canonical.main_equivalence`,
`Canonical.graphSpace_iso_iff_needs_symmetry`,
`Canonical.graphSpace_iso_iff_needs_irreflexive`, `Canonical.graphSpace_core_discrete`,
`Canonical.chain_tendsto_core`, `Canonical.cauchy_tendsto_of_recurrent`,
`Canonical.cauchy_eventually_constant_of_decor`,
`Canonical.core_is_limit_needs_irrational`, `Canonical.E_functor_lipschitz_false`.

`grep -rn "sorry" --include=*.lean . | grep -v '\.lake/'` is empty.

## 5. Scope

**Every numbered result of §§1–5 of the paper is formalized, with no hypotheses and no
omissions.**
Proposition 5.1 is no longer an assumption: `exists_finite_rigid_realizing`
(`RequestProject/Bowtie.lean`) proves it, and `separable_extends_to_extreme'`,
`separable_extends_to_extremePoint'` and `exists_countable_extreme_realizing'`
(`RequestProject/Unconditional.lean`) are the unconditional forms of Theorem 1.1 and
Corollary 1.2.  The hypothesised forms `separable_extends_to_extreme`,
`separable_extends_to_extremePoint` and `exists_countable_extreme_realizing` are kept,
unchanged, since they document the dependency structure; the primed forms are obtained from
them by supplying `exists_finite_rigid_realizing` for `hrat`, with no change to any proof.

### 5.1 What of §§6–7 is in scope, and what is not

Of §6 everything is formalized: the canonical selectors (`def:selectors`), the canonical
extension (`def:canonical`) and functoriality (`thm:functor`).

Of §7 the *metric* content is formalized — isolation (`lem:isolation`), the accumulation of
chains at the core (`lem:limits`), recovery in carrier form (`thm:recovery`) and the
equivalence "`G ≅ H` iff `E(X_G)` and `E(X_H)` are isometric" (`thm:gi` minus the word
"Borel") — and the *descriptive set theory* is not. The following are explicitly **out of
scope**, and the ledger of §7 records them as such rather than leaving blank rows:

* **Borel-ness of the reduction** `G ↦ E(X_G)`, and hence the word "Borel" in `thm:gi`:
  `main_equivalence` proves the equivalence of isomorphism and isometry, which is the
  mathematical content; that the map is Borel in the standard coding of Polish metric
  spaces is a computation about codings that Mathlib has no framework for.
* **`G_δ`-ness of the extreme class** inside `M̄(ℕ) ⊆ [0,1]^{ℕ×ℕ}`, used in the paper to make
  `≅_x` a legitimate restriction of isometry of Polish spaces.
* **Universality of graph isomorphism** among isomorphism relations of countable
  structures, and the **Gao–Kechris theorem** on isometry of Polish metric spaces
  [GaoKechris03], on which Corollary `cor:nonclass` rests.
* **Turbulence** and the resulting obstruction to classification by countable structures
  [Hjorth00], on which Proposition `prop:obstruction` rests.
* **`lem:completion`** (extremality passes to completions), because no completion is
  constructed — see §2.4(21) — and **`carrier_complete`**, of which only the ingredients
  are formalized — see §2.4(20).

Borel reducibility, turbulence and the classification theory of Polish group actions are
not in Mathlib; formalizing them is a project of a different order from this one, and
asserting them here would be exactly the overclaim these ledgers exist to prevent.

## 6. The Tier 4 estimate for `cor:rational-distances`, in retrospect

The Tier 4 return estimated the discharge of `hrat` as a short increment rather than a
campaign, *provided* the companion development were available to transport. It was not
available in Tier 5 either, so the self-contained route was taken, and the estimate still
held: the bowtie family, its membership in `M̄`, the tight-triple catalogue, the full
rigidity argument and the two traps are one file of about four hundred lines. The estimate
below is left as written in Tier 4, for the record.

It reads as a **short increment, not a campaign**, provided `thm:bowtie-general` is
formalized in the strong form the sketch quotes — for each `n ≥ max{5, 2b}` a generalized
bowtie metric on `n` points whose ray is extreme in the metric cone and whose value set on
distinct points is exactly `{1/b, 2/b, …, b/b}` — and `thm:ray-to-point` in the form "a
generator of an extreme ray of the cone with maximum value `1` is an extreme point of the
body". Then the corollary is: given `q = a/b ∈ (0,1)` in lowest terms, instantiate
`thm:bowtie-general` at some admissible `n`, observe `a/b` is in the value set since
`0 < a < b`, apply `thm:ray-to-point`, and handle `q = 1` by the two-point partition metric.
There is no new geometry; the work is (i) turning the value-set statement into "there exist
`u v` with `ρ u v = a/b`", which needs the value set as an equality of sets or at least a
`⊇`, and (ii) reconciling the bridge between the two formalizations' notions of extremality
(cone ray vs. point of `M̄(F)`) with the `Rigid`/`IsBddPseudo` interface used here — a
transport step of the kind already done in `Transport.lean`. The realistic risks are
bookkeeping ones: whether the companion development exposes the value set of the bowtie
metric as a usable lemma rather than only inside a proof, and whether its normalization
matches `max = 1`. If either is missing, the increment grows, but still well short of a
re-proof of `thm:bowtie-general`.

## 7. Coverage ledger

One row per numbered result of `separable-extreme.tex`. The rows of §§6–7 are those of the
revised paper; the two rows this ledger previously carried as "Question 6.1 (`q:density`)"
and "Question 6.2 (`q:canonical`)" belonged to the earlier version, in which §6 was the
questions section. `q:canonical` has since become Theorem `thm:functor` and Question
`q:minimal`, both of which now have rows; `q:density` is unchanged apart from its number.

| paper result | statement | status | Lean name |
|---|---|---|---|
| Theorem 1.1 (`thm:main`) | every separable bounded-by-1 pseudometric space extends, by countably many points, to an extreme one, and the extension is separable | formalized, unconditionally | `separable_extends_to_extreme'`, `separable_extends_to_extremePoint'` (and the hypothesised forms `separable_extends_to_extreme`, `separable_extends_to_extremePoint`) |
| Corollary 1.2 (`cor:irrational`) | for countable `X` an extreme point of `M̄(X)` may realize any prescribed countable subset of `[0,1]` among its distances | formalized, unconditionally | `exists_countable_extreme_realizing'` (and the hypothesised form `exists_countable_extreme_realizing`) |
| Definition 2.1 (`def:perturbation`) | perturbation of `d ∈ M̄(X)` | formalized | `IsPerturbation` |
| Proposition 2.2 (`prop:extreme-iff`) | `d` extreme ⟺ the only perturbation is `0` | formalized | `rigid_iff_extremePoint` |
| Lemma 2.3 (`lem:bound`) | `|ε| ≤ min{d, 1-d}`; `ε = 0` where `d ∈ {0,1}` | formalized | `abs_pert_le`, `pert_eq_zero_of_dist_eq_zero`, `pert_eq_zero_of_dist_eq_one` |
| Lemma 2.4 (`lem:tight`) | a perturbation is additive on a tight triangle | formalized | `pert_add_of_tight` (and `pert_add_of_tight_chain` for chains) |
| Lemma 2.5 (`lem:dense`) | a perturbation vanishing on a dense set vanishes | formalized | `pert_eq_zero_of_dense` |
| Corollary 2.6 (`cor:restrict`) | perturbations restrict; an extreme restriction freezes its subset | formalized | `isPerturbation_restrict`, `pert_eq_zero_on_of_rigid_restrict` |
| Lemma 3.1 (`lem:glue`) | the truncated amalgam along a finite locus is in `M̄`, restricts to both factors, and satisfies the dichotomy | formalized (single piece; and for families: `glueFamily_*`) | `glue_isBddPseudo`, `glue_dichotomy` |
| Remark 3.2 (`rem:pushout`) | without the truncation one gets the pushout, which leaves `M̄` | formalized as the refutation of the untruncated statement | `glue_no_truncation_not_isBddPseudo` |
| Lemma 4.1 (`lem:subdivide`) | a positive distance is subdivided by a countable geodesic chain of rational gaps, and a perturbation is the sum of its values on the gaps | formalized | `exists_rat_seq_hasSum`, `pert_eq_tsum_of_geodesic`, `pert_eq_zero_of_gaps_zero`, `exists_subdivision_extension` |
| Proposition 5.1 (`prop:realize`) | every rational `q ∈ (0,1]` is a distance in a finite extreme metric | formalized | `exists_finite_rigid_realizing` (from `Bowtie.bowtie_isBddPseudo` and `Bowtie.bowtie_rigid`) |
| §5 induction (proof of `thm:main`) | the chain assembly freezing the whole extension | formalized | `rigid_of_chain`, `exists_freezing_extension`, `separable_extends_to_extreme` |
| Definition (`def:selectors`) | canonical selectors: the binary subdivision of an irrational, the canonical piece of a rational | formalized | `Canonical.bit`, `Canonical.cgap`, `Canonical.hasSum_cgap`, `Canonical.ratOf`, and `Stage2.qOf`/`bsz`/`alv` for the piece |
| Definition (`def:canonical`) | the canonical extension `E(A)`, both stages glued over ordered pairs | formalized | `Canonical.ECarrier`, `Canonical.EDist`, with `E_isBddPseudo`, `E_extends`, `E_rigid`, `E_extremePoint` |
| Theorem (`thm:functor`) | `E` is a functor on countable spaces and isometric embeddings | formalized | `Canonical.E_functor`, `E_functor_comp`, `E_functor_surj` |
| Remark (`rem:minimality`) | functoriality and minimality pull apart | not formalized (a remark, not a result) | — |
| Lemma (`lem:completion`) | extremality passes to completions | **not formalized** — no completion is constructed; route (b) of the census, see §2.4(21). Its two inputs are formalized | `isPerturbation_restrict`, `pert_eq_zero_of_dense` (inputs only) |
| Lemma (`lem:isolation`) | every decoration point of `E(A)` is isolated | formalized, in carrier form and with an explicit radius | `Canonical.decor_isolated`, `Canonical.decor_EIsolated` |
| Lemma (`lem:limits`) | the chains accumulate exactly at the core, so the core is definable from the isometry type | formalized in the direction used (core points are limits; decoration points are not); the completeness statement `carrier_complete` is **not formalized** — see §2.4(20) | `Canonical.core_is_limit`, `Canonical.core_not_EIsolated`; ingredients `Canonical.graphSpace_core_discrete`, `chain_tendsto_core`, `cauchy_tendsto_of_recurrent`, `cauchy_eventually_constant_of_decor` |
| Theorem (`thm:recovery`) | an isometry of extensions restricts to an isometry of cores | formalized in carrier form (the commission's (R)), which avoids completions | `Canonical.recovery` |
| Theorem (`thm:gi`), metric content | `G ≅ H` iff the canonical extensions of the graph spaces are isometric | formalized | `Canonical.main_equivalence`, `Canonical.graphSpace_iso_iff` (both for simple graphs — see §2.4(18)) |
| Theorem (`thm:gi`), Borel wrapper | the reduction is Borel, and the extreme class is `G_δ` | **out of scope** — descriptive set theory is not in Mathlib; see §5.1 | — |
| Corollary (`cor:nonclass`) | isometry of extreme Polish spaces is above graph isomorphism, hence not classifiable by countable structures | **out of scope** — rests on universality of `GI` and on [GaoKechris03]; see §5.1 | — |
| Proposition (`prop:obstruction`) | the turbulence obstruction to pushing the reduction further | **out of scope** — rests on [Hjorth00]; see §5.1 | — |
| Question (`q:universal`) | is `≅_x` bireducible with the universal orbit equivalence relation? | not formalized (an open question, not a result) | — |
| Question (`q:density`) | density character `κ` in place of separability | not formalized (an open question, not a result) | — |
| Question (`q:minimal`) | is there a minimal extreme extension? | not formalized (an open question, not a result) | — |

*Improvement to the companion paper.* The single family `B_b = B_{1,2,2,…,2}` of
`RequestProject/Bowtie.lean` realizes **every** rational `q ∈ (0,1]`, superseding the
two-case proof of the companion paper's `cor:rational-distances` (`q = 2`, using
`B_{2,n-2}`, and `q ≥ 3`, using `B_{1,2,…,2,n-2q+1}`) and the paper's own split of
Proposition 5.1 into `q = 1` and `q = a/b` with `0 < a < b`. Writing `q` as
`(2·num)/(2·den)` puts every rational in `(0,1]` in the shape `a/b` with `b ≥ 2` and
`1 ≤ a ≤ b`, which is exactly the value set of `B_b`.
