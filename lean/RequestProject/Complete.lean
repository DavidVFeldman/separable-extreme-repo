import RequestProject.Graph
import RequestProject.Isolation

/-!
# Tier 6d: how close `E(A)` is to being complete

The commission asks for `carrier_complete`: that every Cauchy sequence in `E(X_G)` is
eventually constant or converges to a core point already in the carrier, which is what
licenses the paper's completion-level phrasing of the recovery theorem. **That statement is
not formalized here.** What is formalized are the three mechanisms it is assembled from, and
the two cases they settle outright:

* `graphSpace_core_discrete` — the core of a graph space is uniformly discrete: distinct
  core points are at distance at least `1/√5`;
* `chain_tendsto_core` — the canonical chain over an ordered pair converges to its terminal
  core point, so chains have their limits inside the carrier;
* `cauchy_eventually_constant_of_decor` — a Cauchy sequence that meets a decoration point
  infinitely often is eventually constant (this is `decor_isolated` at work);
* `cauchy_tendsto_of_recurrent` — a Cauchy sequence that meets *any* point infinitely often
  converges to it.

What is missing for the full statement is the remaining case, in which the sequence meets
every point only finitely often: one has to follow the sequence down through the two stages
of the construction (from bowtie points to their anchors, from chain points to theirs) and
show that the anchors are themselves Cauchy and eventually lie in a single chain, whose
positions then converge to the terminal core point. The coverage ledger of `VERIFICATION.md`
records this row as *not formalized* rather than leaving it blank; the carrier-level
`main_equivalence` does not depend on it.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Canonical

universe u

variable {A : Type u} {d : A → A → ℝ}

/-- A Cauchy sequence in `E(A)`. -/
def ECauchy (d : A → A → ℝ) (x : ℕ → ECarrier A d) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → EDist d (x m) (x n) < ε

/-- Convergence in `E(A)`. -/
def ETendsto (d : A → A → ℝ) (x : ℕ → ECarrier A d) (l : ECarrier A d) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → EDist d (x n) l < ε

/-- **The core of a graph space is uniformly discrete.** -/
theorem graphSpace_core_discrete {G : ℕ → ℕ → Prop} {m n : ℕ} (h : m ≠ n) :
    (Real.sqrt 5)⁻¹ ≤ graphSpace G m n := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hle : (Real.sqrt 5)⁻¹ ≤ (Real.sqrt 3)⁻¹ := le_of_lt (inv_strictAnti₀ h3 hlt)
  rcases graphSpace_of_ne (G := G) h with hv | hv <;> rw [hv]
  · exact hle

/-- **A canonical chain converges to its terminal core point**: the limits of the chains are
already in the carrier. -/
theorem chain_tendsto_core (hd : IsBddPseudo d) (p : Chains A d) :
    ETendsto d (fun n => (Sum.inl (chp d p n) : ECarrier A d)) (einl d (cv d p)) := by
  intro ε hε
  have hsum := cgaps_hasSum hd p
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum.tendsto_sum_nat ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hspos : Stage1.spos (cgaps d) p n = ∑ i ∈ Finset.range n, cgaps d p i := rfl
  have hclose : d (cu d p) (cv d p) - Stage1.spos (cgaps d) p n < ε := by
    have h := hN n hn
    rw [Real.dist_eq] at h
    have := abs_lt.mp h
    rw [hspos]
    linarith [this.1]
  have hge : 0 ≤ d (cu d p) (cv d p) - Stage1.spos (cgaps d) p n := by
    have := Stage1.spos_lt (cgaps_pos d) (cgaps_hasSum hd) p n
    linarith
  have h : EDist d (Sum.inl (chp d p n)) (einl d (cv d p))
      = d (cu d p) (cv d p) - Stage1.spos (cgaps d) p n :=
    Stage1.subDist_tail hd (cgaps_pos d) (cgaps_hasSum hd) (a := cgaps d)
      (tu := cu d) (tv := cv d) p n
  rw [h]
  exact hclose

/-- **A Cauchy sequence that meets a point infinitely often converges to it.** -/
theorem cauchy_tendsto_of_recurrent {x : ℕ → ECarrier A d} (hx : ECauchy d x)
    {l : ECarrier A d} (hl : ∀ N, ∃ n, N ≤ n ∧ x n = l) : ETendsto d x l := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, hkl⟩ := hl N
  have := hN n k hn hk
  rwa [hkl] at this

/-- **A Cauchy sequence that meets a decoration point infinitely often is eventually
constant**: decoration points are isolated. -/
theorem cauchy_eventually_constant_of_decor (hd : IsBddPseudo d) {x : ℕ → ECarrier A d}
    (hx : ECauchy d x) {l : ECarrier A d} (hlD : l ∈ Decor A d)
    (hl : ∀ N, ∃ n, N ≤ n ∧ x n = l) : ∃ N, ∀ n, N ≤ n → x n = l := by
  obtain ⟨δ, hδ, hiso⟩ := decor_isolated hd l hlD
  obtain ⟨N, hN⟩ := hx δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, hkl⟩ := hl N
  have hlt : EDist d (x n) l < δ := by
    have := hN n k hn hk
    rwa [hkl] at this
  by_contra hne
  have := hiso (x n) hne
  have hsymm := (E_isBddPseudo hd).symm l (x n)
  linarith [hsymm ▸ this]

end Canonical
