import RequestProject.Perturbation

/-!
# Tier 4a: tight chains and truncation

Two lemmas that the Tier 4 construction rests on.

* `pert_add_of_tight_chain` generalizes `pert_add_of_tight` (paper Lemma 2.4) from one
  intermediate point to a chain of arbitrary finite length.
* `isBddPseudo_min_one` truncates an unbounded pseudometric at `1`.
-/

set_option autoImplicit false

open scoped BigOperators

variable {X : Type*}

namespace IsBddPseudo

/-- The polygon inequality: the distance between the ends of a chain is at most the sum of
the lengths of its links. -/
theorem le_sum_range {d : X → X → ℝ} (hd : IsBddPseudo d) (p : ℕ → X) (m : ℕ) :
    d (p 0) (p m) ≤ ∑ i ∈ Finset.range m, d (p i) (p (i + 1)) := by
  induction m with
  | zero => simp [hd.diag]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      exact le_trans (hd.triangle (p 0) (p m) (p (m + 1))) (by linarith)

/-- If a three-link chain is tight then dropping the first intermediate point leaves a
tight two-link chain. -/
theorem tight_of_tight3 {d : X → X → ℝ} (hd : IsBddPseudo d) {x z z' y : X}
    (h : d x y = d x z + d z z' + d z' y) : d x y = d x z' + d z' y := by
  have h1 : d x z' ≤ d x z + d z z' := hd.triangle x z z'
  have h2 : d x y ≤ d x z' + d z' y := hd.triangle x z' y
  linarith

end IsBddPseudo

/-- A perturbed metric is itself a bounded-by-one pseudometric: it is the midpoint of
`d + ε` and `d - ε`. -/
theorem IsPerturbation.isBddPseudo {d ε : X → X → ℝ} (h : IsPerturbation d ε) :
    IsBddPseudo d := by
  obtain ⟨-, -, hplus, hminus⟩ := h
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
  · have := hplus.nonneg x y; have := hminus.nonneg x y; simp only at *; linarith
  · have := hplus.le_one x y; have := hminus.le_one x y; simp only at *; linarith
  · have := hplus.diag x; have := hminus.diag x; simp only at *; linarith
  · have h1 := hplus.symm x y; have h2 := hminus.symm x y; simp only at h1 h2; linarith
  · have h1 := hplus.triangle x y z; have h2 := hminus.triangle x y z
    simp only at h1 h2; linarith

/-- **Tier 4a.1.** A perturbation is additive along a tight chain of any finite length: if
the distance from `p 0` to `p m` equals the sum of the link lengths, then the perturbation
of the total equals the sum of the perturbations of the links.

The proof splits off the first link: if the whole chain is tight then so is the triangle
`p 0, p 1, p m`, and so is the shortened chain `p 1, …, p m`. -/
theorem pert_add_of_tight_chain (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {m : ℕ} (p : ℕ → X)
    (htight : d (p 0) (p m) = ∑ i ∈ Finset.range m, d (p i) (p (i + 1))) :
    ε (p 0) (p m) = ∑ i ∈ Finset.range m, ε (p i) (p (i + 1)) := by
  have hd : IsBddPseudo d := h.isBddPseudo
  induction m generalizing p with
  | zero => simpa using h.2.1 (p 0)
  | succ m ih =>
      set q : ℕ → X := fun i => p (i + 1) with hq
      have hsplit : d (p 0) (p (m + 1)) =
          d (p 0) (p 1) + ∑ i ∈ Finset.range m, d (q i) (q (i + 1)) := by
        rw [htight, Finset.sum_range_succ' (fun i => d (p i) (p (i + 1))) m]
        simp [hq, add_comm]
      have hchain : d (q 0) (q m) ≤ ∑ i ∈ Finset.range m, d (q i) (q (i + 1)) :=
        hd.le_sum_range q m
      have htri : d (p 0) (p (m + 1)) ≤ d (p 0) (p 1) + d (q 0) (q m) := by
        have := hd.triangle (p 0) (p 1) (p (m + 1))
        simpa [hq] using this
      have htightq : d (q 0) (q m) = ∑ i ∈ Finset.range m, d (q i) (q (i + 1)) := by
        have : d (q 0) (q m) ≥ ∑ i ∈ Finset.range m, d (q i) (q (i + 1)) := by linarith
        linarith
      have htight3 : d (p 0) (p (m + 1)) = d (p 0) (p 1) + d (p 1) (p (m + 1)) := by
        have : d (q 0) (q m) = d (p 1) (p (m + 1)) := by simp [hq]
        rw [hsplit, ← htightq, this]
      have hstep : ε (p 0) (p (m + 1)) = ε (p 0) (p 1) + ε (p 1) (p (m + 1)) :=
        pert_add_of_tight d ε h htight3
      have hih : ε (q 0) (q m) = ∑ i ∈ Finset.range m, ε (q i) (q (i + 1)) := ih q htightq
      have hq0 : ε (q 0) (q m) = ε (p 1) (p (m + 1)) := by simp [hq]
      rw [hstep, ← hq0, hih, Finset.sum_range_succ' (fun i => ε (p i) (p (i + 1))) m]
      simp [hq, add_comm]

/-- **Tier 4a.2.** Truncating a (possibly unbounded) pseudometric at `1` produces a
bounded-by-one pseudometric. -/
theorem isBddPseudo_min_one {ω : X → X → ℝ}
    (hnn : ∀ x y, 0 ≤ ω x y) (hdiag : ∀ x, ω x x = 0) (hsymm : ∀ x y, ω x y = ω y x)
    (htri : ∀ x y z, ω x z ≤ ω x y + ω y z) :
    IsBddPseudo (fun x y => min 1 (ω x y)) := by
  refine ⟨fun x y => le_min zero_le_one (hnn x y), fun x y => min_le_left _ _,
    fun x => by simp [hdiag x], fun x y => by simp only [hsymm x y], fun x y z => ?_⟩
  show min 1 (ω x z) ≤ min 1 (ω x y) + min 1 (ω y z)
  rcases le_or_gt 1 (ω x y) with h | h
  · have h1 : (1:ℝ) ≤ min 1 (ω x y) := le_min le_rfl h
    have h2 : (0:ℝ) ≤ min 1 (ω y z) := le_min zero_le_one (hnn y z)
    have := min_le_left 1 (ω x z)
    linarith
  rcases le_or_gt 1 (ω y z) with h' | h'
  · have h1 : (1:ℝ) ≤ min 1 (ω y z) := le_min le_rfl h'
    have h2 : (0:ℝ) ≤ min 1 (ω x y) := le_min zero_le_one (hnn x y)
    have := min_le_left 1 (ω x z)
    linarith
  · have e1 : min 1 (ω x y) = ω x y := min_eq_right h.le
    have e2 : min 1 (ω y z) = ω y z := min_eq_right h'.le
    rw [e1, e2]
    exact le_trans (min_le_right _ _) (htri x y z)
