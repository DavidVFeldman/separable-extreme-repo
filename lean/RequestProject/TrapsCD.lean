import RequestProject.Construct

/-!
# The two Tier 4 traps

Both statements of §6 of the commission are **false**, and neither is proved here. As in
`RequestProject/Traps.lean`, each is recorded as a commented-out statement together with an
explicit Lean counterexample refuting it.

* **Trap C** — that the finite extreme pieces can be glued on directly, without the
  subdivision stage. It fails as soon as a target distance is irrational: the pieces
  supplied by the hypothesis `hrat` of `separable_extends_to_extreme` realize exactly the
  rational values, so no single gluing can freeze an irrational pair.
* **Trap D** — that a map `ε` vanishing on a dense set is already enough for rigidity (or
  for `ε = 0`), without the hypothesis `IsPerturbation d ε`. The bound `|ε| ≤ d` supplied by
  `IsPerturbation` is exactly what makes `ε` continuous, and without it both readings fail.
-/

set_option autoImplicit false

/-! ### A two-point space -/

/-- The two-point space `Bool` with the two points at distance `c`. -/
noncomputable def boolMetric (c : ℝ) : Bool → Bool → ℝ := fun x y => if x = y then 0 else c

@[simp] theorem boolMetric_self (c : ℝ) (x : Bool) : boolMetric c x x = 0 := by
  simp [boolMetric]

@[simp] theorem boolMetric_false_true (c : ℝ) : boolMetric c false true = c := by
  simp [boolMetric]

theorem boolMetric_isBddPseudo {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    IsBddPseudo (boolMetric c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; unfold boolMetric; split <;> simp [h0]
  · intro x y; unfold boolMetric; split <;> simp [h1]
  · intro x; simp
  · intro x y; unfold boolMetric; by_cases h : x = y <;> simp [h, eq_comm]
  · intro x y z
    unfold boolMetric
    by_cases hxz : x = z
    · simp only [if_pos hxz]
      have : ∀ a b : Bool, 0 ≤ (if a = b then (0:ℝ) else c) := by
        intro a b; split <;> simp [h0]
      linarith [this x y, this y z]
    · simp only [if_neg hxz]
      by_cases hxy : x = y
      · subst hxy
        simp [hxz]
      · simp only [if_neg hxy]
        have : ∀ a b : Bool, 0 ≤ (if a = b then (0:ℝ) else c) := by
          intro a b; split <;> simp [h0]
        linarith [this y z]

theorem boolMetric_add (c c' : ℝ) :
    (fun x y => boolMetric c x y + boolMetric c' x y) = boolMetric (c + c') := by
  funext x y; unfold boolMetric; split <;> simp

theorem boolMetric_sub (c c' : ℝ) :
    (fun x y => boolMetric c x y - boolMetric c' x y) = boolMetric (c - c') := by
  funext x y; unfold boolMetric; split <;> simp

/-! ### Trap C: two stages are not one

```lean
-- FALSE. Not provable, and not proved here.
theorem one_stage_suffices (d : X → X → ℝ) (hd : IsBddPseudo d) …
    (hrat : ∀ q : ℚ, 0 < q → q ≤ 1 → ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
      IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)) :
    Rigid (glueFamily …)
```

i.e. that every target pair of `A` can be frozen by gluing one finite extreme piece onto it,
with no subdivision. The pieces available are exactly those produced by `hrat`, and the pair
they freeze is at a **rational** distance `(q : ℝ)`. So a target at an irrational distance
cannot be matched by any piece, and the single-stage gluing cannot even be set up — which is
why the construction of `Construct.lean` first subdivides each target into rational gaps.

(Mathematically the obstruction is stronger: a finite extreme metric is a vertex of a
polytope cut out by rational inequalities, hence has only rational distances. Only the
consequence that is actually used — the pieces of `hrat` carry rational distances — is
formalized below.)

The counterexample is the two-point space at distance `√2 / 2`. -/

/-- The irrational distance `√2 / 2 ∈ (0, 1)` used by the Trap C counterexample. -/
noncomputable def sqrtHalf : ℝ := Real.sqrt 2 / 2

theorem sqrtHalf_pos : 0 < sqrtHalf := by
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold sqrtHalf
  linarith

theorem sqrtHalf_lt_one : sqrtHalf < 1 := by
  have h : Real.sqrt 2 < 2 := by
    have : Real.sqrt 2 < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq] using this
  unfold sqrtHalf
  linarith

theorem sqrtHalf_irrational : Irrational sqrtHalf := by
  rintro ⟨q, hq⟩
  have h : ((2 * q : ℚ) : ℝ) = Real.sqrt 2 := by
    have : (q : ℝ) = Real.sqrt 2 / 2 := hq
    push_cast
    linarith
  exact irrational_sqrt_two ⟨2 * q, h⟩

/-- The two-point space of the Trap C counterexample is a bounded-by-one pseudometric space,
and `√2 / 2` is one of its distances. -/
theorem trapC_isBddPseudo : IsBddPseudo (boolMetric sqrtHalf) :=
  boolMetric_isBddPseudo sqrtHalf_pos.le sqrtHalf_lt_one.le

/-- **Trap C fails.** No piece supplied by the hypothesis `hrat` of
`separable_extends_to_extreme` realizes the distance of the two-point space
`boolMetric sqrtHalf`: those pieces realize the rational values `(q : ℝ)` only, and
`√2 / 2` is irrational. Hence the target pair `(false, true)` cannot be frozen by a single
family gluing, and the subdivision stage is not removable. -/
theorem trapC_no_piece_realizes (q : ℚ) :
    (q : ℝ) ≠ boolMetric sqrtHalf false true := by
  simpa using fun h => sqrtHalf_irrational ⟨q, h⟩

/-! ### Trap D: density is not enough on its own

```lean
-- FALSE. Not provable, and not proved here.
theorem dense_zero_implies_rigid (d ε : X → X → ℝ) {A : Set X} (hA : DenseFor d A)
    (hzero : ∀ a ∈ A, ∀ b ∈ A, ε a b = 0) : Rigid d

-- FALSE. Not provable, and not proved here.
theorem dense_zero_implies_zero (d ε : X → X → ℝ) {A : Set X} (hA : DenseFor d A)
    (hzero : ∀ a ∈ A, ∀ b ∈ A, ε a b = 0) : ∀ x y, ε x y = 0
```

Both are `pert_eq_zero_of_dense` with the hypothesis `IsPerturbation d ε` deleted; that
hypothesis is what supplies the bound `|ε| ≤ d` and hence the continuity of `ε`. Each
reading is refuted below on the two-point space. -/

/-- The perturbation refuting the first reading of Trap D: on the two-point space at
distance `1/2`, the map `boolMetric (1/4)` is a nonzero perturbation. -/
theorem trapD_isPerturbation :
    IsPerturbation (boolMetric (1/2)) (boolMetric (1/4)) := by
  refine ⟨fun x y => (boolMetric_isBddPseudo (c := (1:ℝ)/4) (by norm_num) (by norm_num)).symm x y,
    fun x => boolMetric_self _ x, ?_, ?_⟩
  · rw [boolMetric_add]
    exact boolMetric_isBddPseudo (by norm_num) (by norm_num)
  · rw [boolMetric_sub]
    exact boolMetric_isBddPseudo (by norm_num) (by norm_num)

/-- **Trap D fails, first reading.** The whole space is dense and the zero map vanishes on
it, yet the two-point space at distance `1/2` is not rigid. -/
theorem trapD_dense_zero_not_rigid :
    DenseFor (boolMetric (1/2)) (Set.univ : Set Bool) ∧
      (∀ a ∈ (Set.univ : Set Bool), ∀ b ∈ (Set.univ : Set Bool),
        (fun _ _ : Bool => (0:ℝ)) a b = 0) ∧
      ¬ Rigid (boolMetric (1/2)) := by
  refine ⟨?_, fun a _ b _ => rfl, ?_⟩
  · intro x η hη
    exact ⟨x, Set.mem_univ x, by simpa using hη⟩
  · intro hR
    have := hR _ trapD_isPerturbation false true
    rw [boolMetric_false_true] at this
    norm_num at this

/-- **Trap D fails, second reading.** On the two-point space carrying the zero pseudometric
the singleton `{false}` is dense, and the map `boolMetric 1` vanishes on it, yet is not
identically zero. (It is of course not a perturbation of the zero pseudometric.) -/
theorem trapD_dense_zero_not_zero :
    DenseFor (boolMetric 0) ({false} : Set Bool) ∧
      (∀ a ∈ ({false} : Set Bool), ∀ b ∈ ({false} : Set Bool), boolMetric 1 a b = 0) ∧
      ¬ (∀ x y : Bool, boolMetric 1 x y = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x η hη
    refine ⟨false, rfl, ?_⟩
    unfold boolMetric
    split <;> simpa using hη
  · rintro a rfl b rfl
    simp
  · intro h
    have := h false true
    rw [boolMetric_false_true] at this
    norm_num at this
