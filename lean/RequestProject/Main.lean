import Mathlib
import RequestProject.Perturbation
import RequestProject.Glue
import RequestProject.Subdivide
import RequestProject.Traps
import RequestProject.Chain
import RequestProject.Transport
import RequestProject.GlueFamily
import RequestProject.Subdivision
import RequestProject.Freeze
import RequestProject.Construct
import RequestProject.Corollary
import RequestProject.TrapsCD
import RequestProject.Bowtie
import RequestProject.TrapsEF
import RequestProject.Unconditional
import RequestProject.Bits
import RequestProject.GlueTransport
import RequestProject.Stage1
import RequestProject.Stage2
import RequestProject.Canonical
import RequestProject.Functor
import RequestProject.LowerBounds
import RequestProject.StageIsolation
import RequestProject.Isolation
import RequestProject.Graph
import RequestProject.Complete
import RequestProject.TrapsGH

/-!
# Every Separable Metric Space Extends to an Extreme One

This file collects the formalization and records the axiom audit.

* `RequestProject/Perturbation.lean` — §2 of the paper: the convex set of bounded-by-one
  pseudometrics, the equivalence of rigidity with extremality (Proposition 2.2), the
  perturbation bound (Lemma 2.3), tight triangles (Lemma 2.4), density (Lemma 2.5) and
  restriction (Corollary 2.6).
* `RequestProject/Glue.lean` — §3: the amalgam along a finite gluing locus and its
  dichotomy (Lemma 3.1).
* `RequestProject/Subdivide.lean` — §4 and the §5 induction: subdivision of a positive real
  into positive rationals, the geodesic summation lemma (Lemma 4.1(3)) and the inductive
  assembly `rigid_of_chain`.
* `RequestProject/Traps.lean` — the two Tier 1–3 false strengthenings, recorded as
  commented-out statements together with Lean counterexamples refuting them.
* `RequestProject/Chain.lean` — Tier 4a: additivity of a perturbation along a tight chain
  (`pert_add_of_tight_chain`) and the truncation `isBddPseudo_min_one`.
* `RequestProject/Transport.lean` — transport of pseudometrics, perturbations and rigidity
  along maps.
* `RequestProject/GlueFamily.lean` — Tier 4b: the simultaneous gluing of a family of finite
  pieces, its pseudometric axioms, its restrictions and its two dichotomies.
* `RequestProject/Subdivision.lean` — stage 1 of the construction: every target pair is
  subdivided into a countable chain of rational gaps.
* `RequestProject/Freeze.lean` — stage 2: a finite rigid piece is glued onto every gap pair.
* `RequestProject/Construct.lean` — Tier 4c: Theorem 1.1, `separable_extends_to_extreme`
  (and its extreme-point form).
* `RequestProject/Corollary.lean` — Corollary 1.2, `exists_countable_extreme_realizing`.
* `RequestProject/TrapsCD.lean` — the two Tier 4 false strengthenings (Traps C and D),
  again recorded as commented-out statements with Lean counterexamples.
* `RequestProject/Bowtie.lean` — Tier 5: the bowtie family `B_b`, its rigidity, and
  Proposition 5.1 (`exists_finite_rigid_realizing`), which discharges the hypothesis `hrat`.
* `RequestProject/TrapsEF.lean` — the two Tier 5 false strengthenings (Traps E and F),
  again recorded as commented-out statements with Lean counterexamples.
* `RequestProject/Unconditional.lean` — Tier 5: Theorem 1.1 and Corollary 1.2 restated
  without `hrat`.
* `RequestProject/Bits.lean` — Tier 6a: the canonical selectors — binary digits, the
  canonical gap sequence of an irrational number, and the canonical rational.
* `RequestProject/GlueTransport.lean` — transport of the family amalgam along a map of
  gluing data, and piece data from a uniform family of piece metrics.
* `RequestProject/Stage1.lean`, `RequestProject/Stage2.lean` — the two stages of the
  construction on explicit carriers, refactored by addition from the existential Tier 4
  interfaces.
* `RequestProject/Canonical.lean` — Tier 6b: the canonical extension `E(A)`, with
  `E_isBddPseudo`, `E_extends` and `E_rigid`.
* `RequestProject/Functor.lean` — Tier 6b: functoriality, `E_functor`, `E_functor_comp` and
  `E_functor_surj`.
* `RequestProject/LowerBounds.lean`, `RequestProject/StageIsolation.lean` — the isolation
  estimates for the amalgam, the bowtie and the two stages.
* `RequestProject/Isolation.lean` — Tier 6c: `decor_isolated`, `core_is_limit` and
  `recovery` in carrier form.
* `RequestProject/Graph.lean` — Tier 6d: the graph spaces, `graphSpace_iso_iff` and
  `main_equivalence` (the paper's Theorem 7.6 minus the word "Borel"), together with the two
  refutations showing that the simple-graph hypotheses cannot be dropped.
* `RequestProject/Complete.lean` — Tier 6d: the ingredients of `carrier_complete` that are
  formalized (uniform discreteness of the core, convergence of chains, and the two recurrent
  cases); the full statement is recorded as not formalized.
* `RequestProject/TrapsGH.lean` — the two Tier 6 false strengthenings (Traps G and H),
  again recorded as commented-out statements with Lean refutations.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

-- Axiom audit for the closure criteria of the commission, Tiers 1–3.
#print axioms rigid_iff_extremePoint
#print axioms pert_eq_zero_of_dense
#print axioms glue_isBddPseudo
#print axioms glue_dichotomy
#print axioms pert_eq_tsum_of_geodesic
#print axioms rigid_of_chain
#print axioms glue_no_truncation_not_isBddPseudo
#print axioms glue_dichotomy_infinite_false

-- Axiom audit for Tier 4.
#print axioms pert_add_of_tight_chain
#print axioms isBddPseudo_min_one
#print axioms glueFamily_isBddPseudo
#print axioms glueFamily_restrict_base
#print axioms glueFamily_restrict_piece
#print axioms glueFamily_dichotomy_base_piece
#print axioms glueFamily_dichotomy_piece_piece
#print axioms exists_subdivision_extension
#print axioms exists_freezing_extension
#print axioms separable_extends_to_extreme
#print axioms separable_extends_to_extremePoint
#print axioms exists_countable_extreme_realizing

-- Axiom audit for the Tier 4 trap counterexamples.
#print axioms trapC_no_piece_realizes
#print axioms trapD_dense_zero_not_rigid
#print axioms trapD_dense_zero_not_zero

-- Axiom audit for Tier 5.
#print axioms exists_finite_rigid_realizing
#print axioms Bowtie.bowtie_isBddPseudo
#print axioms Bowtie.bowtie_rigid
#print axioms separable_extends_to_extreme'
#print axioms separable_extends_to_extremePoint'
#print axioms exists_countable_extreme_realizing'

-- Axiom audit for the Tier 5 trap counterexamples.
#print axioms TrapE.trapE_bowtie22_not_rigid
#print axioms trapF_bowtieRaw_not_isBddPseudo

-- Axiom audit for Tier 6a: the canonical selectors.
#print axioms Canonical.bit_mem
#print axioms Canonical.hasSum_bits
#print axioms Canonical.bits_infinite
#print axioms Canonical.hasSum_cgap
#print axioms Canonical.ratOf_spec

-- Axiom audit for Tier 6b: the canonical extension and its functoriality.
#print axioms Canonical.E_isBddPseudo
#print axioms Canonical.E_extends
#print axioms Canonical.E_rigid
#print axioms Canonical.E_extremePoint
#print axioms Canonical.E_functor
#print axioms Canonical.E_functor_comp
#print axioms Canonical.E_functor_surj

-- Axiom audit for Tier 6c: isolation, limits, recovery.
#print axioms Canonical.decor_isolated
#print axioms Canonical.core_is_limit
#print axioms Canonical.recovery

-- Axiom audit for Tier 6d: the graph reduction.
#print axioms Canonical.graphSpace_isBddPseudo
#print axioms Canonical.graphSpace_iso_iff
#print axioms Canonical.main_equivalence
#print axioms Canonical.graphSpace_iso_iff_needs_symmetry
#print axioms Canonical.graphSpace_iso_iff_needs_irreflexive
#print axioms Canonical.graphSpace_core_discrete
#print axioms Canonical.chain_tendsto_core
#print axioms Canonical.cauchy_tendsto_of_recurrent
#print axioms Canonical.cauchy_eventually_constant_of_decor

-- Axiom audit for the Tier 6 trap refutations.
#print axioms Canonical.core_is_limit_needs_irrational
#print axioms Canonical.E_functor_lipschitz_false
