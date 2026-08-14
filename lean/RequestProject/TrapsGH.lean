import RequestProject.Graph
import RequestProject.Isolation

/-!
# Tier 6 traps: two false strengthenings of the canonical extension

Neither statement below is proved; each is recorded as a commented-out statement together
with a Lean refutation.

* **Trap G — recovery without the irrationality hypothesis.** The recovery theorem is proved
  by characterizing the core of `E(A)` as the set of *non-isolated* points, and that
  characterization needs every point of `A` to have a partner at irrational distance:
  without it a core point can be isolated, and then nothing distinguishes it from a
  decoration point. `Canonical.core_is_limit_needs_irrational` exhibits such a space: the
  two-point space at distance `1/2`, all of whose distances are rational, in which the core
  point is isolated in `E(A)` with radius `1/4`. (As the commission notes, refuting the
  characterization is what is required; a `recovery`-shaped counterexample would need an
  exotic isometry and is not claimed here.)

* **Trap H — functoriality for `1`-Lipschitz maps.** `E_functor` needs `ψ` to *preserve*
  distances, not merely not to increase them. `Canonical.E_functor_lipschitz_false` refutes
  the weakened statement: the identity from the graph space of the complete graph to the
  graph space of the empty graph is `1`-Lipschitz (`1/√5 < 1/√3`), and a distance-preserving
  `Ψ` extending it would already force `1/√5 = 1/√3` on the core. This is a simplification of
  the refutation suggested in the commission, which computes the first canonical gaps of the
  two distances: the contradiction is visible on the core, before any chain point is
  reached.
-/

set_option autoImplicit false

namespace Canonical

/-! ## Trap G: recovery without the irrationality hypothesis

```lean
-- FALSE. Must not be provable.
theorem recovery_no_hyp {A B : Type} {dA : A → A → ℝ} {dB : B → B → ℝ}
    (hdA : IsBddPseudo dA) (hdB : IsBddPseudo dB)
    (Φ : ECarrier A dA → ECarrier B dB) (hbij : Function.Bijective Φ)
    (hiso : ∀ x y, EDist dB (Φ x) (Φ y) = EDist dA x y) :
    ∃ φ : A → B, Function.Bijective φ ∧ (∀ a a', dB (φ a) (φ a') = dA a a') ∧
      ∀ a, Φ (einl dA a) = einl dB (φ a)
```
-/

/-- The two-point space at distance `1/2`: all its distances are rational, so no point has
a partner at irrational distance. -/
noncomputable def dhalf (x y : Bool) : ℝ := if x = y then 0 else 1 / 2

theorem dhalf_isBddPseudo : IsBddPseudo dhalf where
  nonneg x y := by cases x <;> cases y <;> norm_num [dhalf]
  le_one x y := by cases x <;> cases y <;> norm_num [dhalf]
  diag x := by cases x <;> norm_num [dhalf]
  symm x y := by cases x <;> cases y <;> norm_num [dhalf]
  triangle x y z := by cases x <;> cases y <;> cases z <;> norm_num [dhalf]

theorem dhalf_not_irrational (x y : Bool) : ¬ Irrational (dhalf x y) := by
  by_cases h : x = y
  · simp only [dhalf, if_pos h]
    rw [show ((0 : ℝ)) = ((0 : ℚ) : ℝ) by norm_num]
    exact Rat.not_irrational _
  · simp only [dhalf, if_neg h]
    rw [show ((1 : ℝ) / 2) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact Rat.not_irrational _

/-- There are no canonical chains over the two-point rational space. -/
theorem dhalf_no_chains (p : Chains Bool dhalf) : False :=
  dhalf_not_irrational _ _ p.property

/-- Every bowtie glued onto the two-point rational space has size `4`. -/
theorem dhalf_bsz (j : Bows Bool dhalf) :
    Stage2.bsz (dist1 dhalf) (banc dhalf) j = 4 := by
  match j with
  | Sum.inr (p, n, o) => exact (dhalf_no_chains p).elim
  | Sum.inl p =>
      have hval : dhalf p.val.1 p.val.2 = 1 / 2 := by
        have hpos := p.property.2
        by_cases h : p.val.1 = p.val.2
        · rw [show dhalf p.val.1 p.val.2 = 0 by simp only [dhalf, if_pos h]] at hpos
          norm_num at hpos
        · simp only [dhalf, if_neg h]
      have hq : Stage2.qOf (dist1 dhalf) (banc dhalf) (Sum.inl p) = 1 / 2 := by
        have h : dist1 dhalf (banc dhalf (Sum.inl p) false) (banc dhalf (Sum.inl p) true)
            = dhalf p.val.1 p.val.2 := rfl
        rw [Stage2.qOf, h, hval, show ((1 : ℝ) / 2) = ((1 / 2 : ℚ) : ℝ) by norm_num,
          ratOf_cast]
      rw [Stage2.bsz, hq]
      norm_num

/-- **Trap G, refuted**: in the two-point rational space the core point is *isolated* in
`E(A)`, with radius `1/4`; so without the irrationality hypothesis the core is not the set
of non-isolated points, and the proof of `recovery` breaks down at its first step. -/
theorem dhalf_core_isolated {y : ECarrier Bool dhalf} (hy : y ≠ einl dhalf false) :
    (1 : ℝ) / 4 ≤ EDist dhalf (einl dhalf false) y := by
  classical
  have hd1 : IsBddPseudo (dist1 dhalf) := dist1_isBddPseudo dhalf_isBddPseudo
  refine glueFamily_base_isolated (by norm_num) (Sum.inl false) ?_ ?_ hy
  · rintro (a | ⟨p, n⟩)
    · cases a
      · exact Or.inl rfl
      · right
        show (1 : ℝ) / 4 ≤ dhalf false true
        norm_num [dhalf]
    · exact (dhalf_no_chains p).elim
  · intro z l
    have h1 := Stage2.inv_bsz_le_pieceAnc hd1 (banc_pos dhalf_isBddPseudo)
      (banc_rat dhalf_isBddPseudo) z l
    rw [dhalf_bsz (Stage2.dIdx z)] at h1
    have h2 : (0 : ℝ) ≤ dist1 dhalf (Sum.inl false) (banc dhalf (Stage2.dIdx z) l) :=
      hd1.nonneg _ _
    have h3 : ((4 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 4 := by norm_num
    rw [h3] at h1
    linarith

/-- **Trap G, refuted** (the statement in the shape of the commission): there is a
bounded-by-one pseudometric space with an isolated core point in its canonical extension. -/
theorem core_is_limit_needs_irrational :
    ∃ (A : Type) (d : A → A → ℝ) (a : A), IsBddPseudo d ∧ EIsolated d (einl d a) := by
  refine ⟨Bool, dhalf, false, dhalf_isBddPseudo, 1 / 4, by norm_num, fun y hy => ?_⟩
  by_cases h : y = einl dhalf false
  · subst h
    exact (E_isBddPseudo dhalf_isBddPseudo).diag _
  · exact absurd (dhalf_core_isolated h) (by linarith)

/-! ## Trap H: functoriality for `1`-Lipschitz maps

```lean
-- FALSE. Must not be provable.
theorem E_functor_lipschitz {A B : Type} {dA : A → A → ℝ} {dB : B → B → ℝ} (ψ : A → B)
    (hψ : ∀ a a', dB (ψ a) (ψ a') ≤ dA a a') (hinj : Function.Injective ψ) :
    ∃ Ψ : ECarrier A dA → ECarrier B dB,
      Function.Injective Ψ ∧ (∀ a, Ψ (einl dA a) = einl dB (ψ a)) ∧
        ∀ x y, EDist dB (Ψ x) (Ψ y) = EDist dA x y
```
-/

/-- **Trap H, refuted**: the identity from the graph space of the complete graph to the
graph space of the empty graph is `1`-Lipschitz, but no distance-preserving map of the
canonical extensions extends it — the two core distances `1/√3` and `1/√5` already differ. -/
theorem E_functor_lipschitz_false :
    ¬ (∀ (A B : Type) (dA : A → A → ℝ) (dB : B → B → ℝ) (ψ : A → B),
        (∀ a a', dB (ψ a) (ψ a') ≤ dA a a') → Function.Injective ψ →
        ∃ Ψ : ECarrier A dA → ECarrier B dB,
          Function.Injective Ψ ∧ (∀ a, Ψ (einl dA a) = einl dB (ψ a)) ∧
            ∀ x y, EDist dB (Ψ x) (Ψ y) = EDist dA x y) := by
  intro hcon
  set dA : ℕ → ℕ → ℝ := graphSpace (fun _ _ => True) with hdA
  set dB : ℕ → ℕ → ℝ := graphSpace (fun _ _ => False) with hdB
  have hA01 : dA 0 1 = (Real.sqrt 3)⁻¹ := by
    simp [hdA, graphSpace]
  have hB01 : dB 0 1 = (Real.sqrt 5)⁻¹ := by
    simp [hdB, graphSpace]
  have hlip : ∀ a a' : ℕ, dB (id a) (id a') ≤ dA a a' := by
    intro a a'
    by_cases h : a = a'
    · subst h; simp [hdA, hdB]
    · rw [show dA a a' = (Real.sqrt 3)⁻¹ by simp [hdA, graphSpace, h],
        show dB (id a) (id a') = (Real.sqrt 5)⁻¹ by simp [hdB, graphSpace, h]]
      have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have hlt : Real.sqrt 3 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      exact le_of_lt (inv_strictAnti₀ h3 hlt)
  obtain ⟨Ψ, -, hcore, hiso⟩ := hcon ℕ ℕ dA dB id hlip Function.injective_id
  have h1 : EDist dB (Ψ (einl dA 0)) (Ψ (einl dA 1)) = EDist dA (einl dA 0) (einl dA 1) :=
    hiso _ _
  rw [hcore 0, hcore 1] at h1
  simp only [E_extends, id_eq] at h1
  rw [hA01, hB01] at h1
  exact sqrt3_inv_ne_sqrt5_inv h1.symm

end Canonical
