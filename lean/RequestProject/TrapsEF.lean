import RequestProject.Bowtie

/-!
# Tier 5 traps: two false strengthenings of the bowtie construction

Neither statement below is proved; each is recorded as a commented-out statement together
with a Lean counterexample refuting it.

* **Trap E — the size hypothesis is not decorative.** The four-point bowtie `B_{2,2}`, whose
  graph is the four-cycle `C₄`, is *not* rigid, so the first cell of the family `B_b` of
  `Bowtie.lean` cannot be allowed to have two points as well.
* **Trap F — the normalization is load-bearing.** The unscaled bowtie takes the value `2`
  between two points of the same level, so it is not a bounded-by-one pseudometric and the
  division by `b` cannot be dropped.
-/

set_option autoImplicit false

/-! ## Trap E: the four-point bowtie `B_{2,2}` is not rigid -/

namespace TrapE

/-- The normalized four-point bowtie `B_{2,2}`: the carrier is `Bool × Bool`, the first
coordinate naming the cell and the second the point inside it.  Two points of a cell are at
distance `1`, two points of different cells at distance `1/2`.  (This is the raw bowtie
metric of two cells of size two, divided by `b = 2`.) -/
noncomputable def d22 (x y : Bool × Bool) : ℝ :=
  if x = y then 0 else if x.1 = y.1 then 1 else 1 / 2

/-- The nonzero perturbation of `d22`: `t = 1/2` on the two "parallel" diagonals of the
four-cycle and `-t` on the other two.  Every triangle that was tight stays tight, since
`(1/2 + t) + (1/2 - t) = 1`. -/
noncomputable def eps22 (x y : Bool × Bool) : ℝ :=
  if x.1 = y.1 then 0 else if x.2 = y.2 then 1 / 2 else -(1 / 2)

theorem d22_isBddPseudo : IsBddPseudo d22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> norm_num [d22]
  · rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> norm_num [d22]
  · rintro ⟨x1, x2⟩
    simp [d22]
  · rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> norm_num [d22]
  · rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨z1, z2⟩
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> cases z1 <;> cases z2 <;>
      norm_num [d22]

theorem eps22_isPerturbation : IsPerturbation d22 eps22 := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨x1, x2⟩ ⟨y1, y2⟩
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> norm_num [eps22]
  · rintro ⟨x1, x2⟩
    simp [eps22]
  all_goals (
    first
      | (rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨z1, z2⟩
         cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> cases z1 <;> cases z2 <;>
           norm_num [d22, eps22])
      | (rintro ⟨x1, x2⟩ ⟨y1, y2⟩
         cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> norm_num [d22, eps22])
      | (rintro ⟨x1, x2⟩
         cases x1 <;> cases x2 <;> norm_num [d22, eps22]))

theorem eps22_ne_zero : eps22 (false, false) (true, false) ≠ 0 := by
  norm_num [eps22]

/-
**Trap E, the false statement.** It must NOT be provable:

theorem bowtie22_rigid : Rigid d22
-/

/-- **Trap E fails.** The four-point bowtie is not rigid: `eps22` is a nonzero
perturbation of it. -/
theorem trapE_bowtie22_not_rigid : ¬ Rigid d22 := by
  intro h
  exact eps22_ne_zero (h eps22 eps22_isPerturbation _ _)

end TrapE

/-! ## Trap F: the unscaled bowtie is not bounded by one -/

/-
**Trap F, the false statement.** It must NOT be provable:

theorem bowtieRaw_isBddPseudo (b : ℕ) : IsBddPseudo (Bowtie.raw b)
-/

/-- **Trap F fails.** For `b ≥ 2` the unscaled bowtie takes the value `2` between the two
points of level `1`, so it is not a bounded-by-one pseudometric: the division by `b` in
`Bowtie.bowtie` cannot be dropped. -/
theorem trapF_bowtieRaw_not_isBddPseudo (b : ℕ) (hb : 2 ≤ b) : ¬ IsBddPseudo (Bowtie.raw b) := by
  intro h
  have hb0 : 0 < b := by omega
  have hne : Bowtie.pt (⟨0, hb0⟩ : Fin b) false ≠ Bowtie.pt (⟨0, hb0⟩ : Fin b) true := Bowtie.pt_ne
  have h2 : Bowtie.raw b (Bowtie.pt (⟨0, hb0⟩ : Fin b) false) (Bowtie.pt (⟨0, hb0⟩ : Fin b) true)
      = 2 := Bowtie.raw_of_lvl_eq rfl hne
  have := h.le_one (Bowtie.pt (⟨0, hb0⟩ : Fin b) false) (Bowtie.pt (⟨0, hb0⟩ : Fin b) true)
  rw [h2] at this
  norm_num at this
