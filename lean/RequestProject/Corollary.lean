import RequestProject.Construct

/-!
# Corollary 1.2: prescribed countable distance sets

An extreme point of `M̄(X)` on a countable `X` may realize any prescribed countable set of
values in `[0,1]` among its distances — irrational values included.

The proof is the paper's: realize the prescribed set as the distance set of the explicit
ultrametric `d(p_*, p_v) = v`, `d(p_v, p_w) = max {v, w}` on a countable space, and apply
Theorem 1.1.
-/

set_option autoImplicit false

open scoped BigOperators

/-- The ultrametric of the paper's proof of Corollary 1.2: a base point `none` together with
one point `some v` for each prescribed value `v`. -/
noncomputable def prescribedUltrametric (V : Set ℝ) : Option ↥V → Option ↥V → ℝ :=
  fun x y => if x = y then 0 else max (Option.elim x 0 (fun v => (v : ℝ)))
    (Option.elim y 0 (fun v => (v : ℝ)))

theorem prescribedUltrametric_isBddPseudo {V : Set ℝ} (hV0 : ∀ v ∈ V, 0 ≤ v)
    (hV1 : ∀ v ∈ V, v ≤ 1) : IsBddPseudo (prescribedUltrametric V) := by
  classical
  set f : Option ↥V → ℝ := fun x => Option.elim x 0 (fun v => (v : ℝ)) with hf
  have hf0 : ∀ x, 0 ≤ f x := by
    rintro (_ | ⟨v, hv⟩)
    · simp [hf]
    · simpa [hf] using hV0 v hv
  have hf1 : ∀ x, f x ≤ 1 := by
    rintro (_ | ⟨v, hv⟩)
    · simp [hf]
    · simpa [hf] using hV1 v hv
  have hval : ∀ x y, prescribedUltrametric V x y = if x = y then 0 else max (f x) (f y) :=
    fun x y => rfl
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
  · rw [hval]
    split
    · exact le_rfl
    · exact le_max_of_le_left (hf0 x)
  · rw [hval]
    split
    · exact zero_le_one
    · exact max_le (hf1 x) (hf1 y)
  · rw [hval, if_pos rfl]
  · rw [hval, hval]
    by_cases h : x = y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), max_comm]
  · have hnn : ∀ u v, 0 ≤ prescribedUltrametric V u v := by
      intro u v
      rw [hval]
      split
      · exact le_rfl
      · exact le_max_of_le_left (hf0 u)
    by_cases hxz : x = z
    · rw [hval, if_pos hxz]
      exact add_nonneg (hnn x y) (hnn y z)
    by_cases hxy : x = y
    · subst hxy
      have : prescribedUltrametric V x x = 0 := by rw [hval, if_pos rfl]
      rw [this, zero_add]
    by_cases hyz : y = z
    · subst hyz
      have : prescribedUltrametric V y y = 0 := by rw [hval, if_pos rfl]
      rw [this, add_zero]
    · rw [hval, hval, hval, if_neg hxz, if_neg hxy, if_neg hyz]
      have h1 : max (f x) (f z) ≤ max (f x) (f y) + max (f y) (f z) := by
        refine max_le ?_ ?_
        · exact le_add_of_le_of_nonneg (le_max_left _ _)
            (le_trans (hf0 y) (le_max_left _ _))
        · exact le_add_of_nonneg_of_le (le_trans (hf0 x) (le_max_left _ _)) (le_max_right _ _)
      exact h1

/-- **Paper Corollary 1.2.** For any countable set `V ⊆ [0,1]` there is a countable space
carrying an extreme (rigid) bounded-by-one pseudometric all of whose prescribed values
`v ∈ V` occur as distances. -/
theorem exists_countable_extreme_realizing (V : Set ℝ) (hV : V.Countable)
    (hV0 : ∀ v ∈ V, 0 ≤ v) (hV1 : ∀ v ∈ V, v ≤ 1)
    (hrat : ∀ q : ℚ, 0 < q → q ≤ 1 →
      ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
        IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)) :
    ∃ (Ω : Type) (dt : Ω → Ω → ℝ),
      Countable Ω ∧ IsBddPseudo dt ∧ Rigid dt ∧
      dt ∈ (bddPseudoSet Ω).extremePoints ℝ ∧
      ∀ v ∈ V, ∃ x y : Ω, dt x y = v := by
  classical
  haveI := hV.to_subtype
  set d0 := prescribedUltrametric V with hd0
  have hd0p : IsBddPseudo d0 := prescribedUltrametric_isBddPseudo hV0 hV1
  have hdense : DenseFor d0 Set.univ := by
    intro x η hη
    exact ⟨x, Set.mem_univ x, by rw [hd0p.diag]; exact hη⟩
  obtain ⟨Ω, ι, dt, hinj, hcount, hdtp, hrig, hres⟩ :=
    separable_extends_to_extreme d0 hd0p (Set.countable_univ) hdense hrat
  have hΩ : Countable Ω := by
    have h1 : (Set.univ : Set Ω).Countable := by
      have : (Set.univ : Set Ω) = Set.range ι ∪ (Set.range ι)ᶜ := by
        rw [Set.union_compl_self]
      rw [this]
      exact (Set.countable_range ι).union hcount
    exact Set.countable_univ_iff.mp h1
  refine ⟨Ω, dt, hΩ, hdtp, hrig, (rigid_iff_extremePoint dt hdtp).mp hrig, ?_⟩
  intro v hv
  refine ⟨ι none, ι (some ⟨v, hv⟩), ?_⟩
  rw [hres]
  show (if (none : Option ↥V) = some ⟨v, hv⟩ then (0:ℝ) else
    max (Option.elim (none : Option ↥V) 0 (fun w => (w : ℝ)))
      (Option.elim (some (⟨v, hv⟩ : ↥V)) 0 (fun w => (w : ℝ)))) = v
  rw [if_neg (by simp)]
  simpa using max_eq_right (hV0 v hv)
