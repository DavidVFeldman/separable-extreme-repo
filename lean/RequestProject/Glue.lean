import RequestProject.Perturbation

/-!
# Gluing along a finite set

Formalization of §3 of *Every Separable Metric Space Extends to an Extreme One*
(Feldman–Kehoe), paper Lemma 3.1.

The amalgam is modelled concretely, to avoid quotient types: `P` and `Q` are the two "new"
parts, `F` is the finite nonempty intersection, and the glued carrier is `P ⊕ F ⊕ Q`. The
two input metrics live on `P ⊕ F` and `F ⊕ Q`.
-/

set_option autoImplicit false

variable {P Q F : Type*} [Fintype F] [Nonempty F]

/-- The cross distance of the amalgam: the truncated minimum over the gluing locus `F`. -/
noncomputable def glueCross (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ)
    (x : P) (y : Q) : ℝ :=
  min 1 ((Finset.univ : Finset F).inf' Finset.univ_nonempty
    (fun z => d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y)))

/-- The amalgamated metric on `P ⊕ F ⊕ Q`. -/
noncomputable def glue (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) :
    (P ⊕ F ⊕ Q) → (P ⊕ F ⊕ Q) → ℝ
  | Sum.inl x, Sum.inl x' => d (Sum.inl x) (Sum.inl x')
  | Sum.inl x, Sum.inr (Sum.inl z) => d (Sum.inl x) (Sum.inr z)
  | Sum.inl x, Sum.inr (Sum.inr y) => glueCross d ρ x y
  | Sum.inr (Sum.inl z), Sum.inl x => d (Sum.inr z) (Sum.inl x)
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inl z') => d (Sum.inr z) (Sum.inr z')
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inr y) => ρ (Sum.inl z) (Sum.inr y)
  | Sum.inr (Sum.inr y), Sum.inl x => glueCross d ρ x y
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inl z) => ρ (Sum.inr y) (Sum.inl z)
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inr y') => ρ (Sum.inr y) (Sum.inr y')

section

variable (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ)

@[simp] theorem glue_PP (x x' : P) :
    glue d ρ (Sum.inl x) (Sum.inl x') = d (Sum.inl x) (Sum.inl x') := rfl
@[simp] theorem glue_PF (x : P) (z : F) :
    glue d ρ (Sum.inl x) (Sum.inr (Sum.inl z)) = d (Sum.inl x) (Sum.inr z) := rfl
@[simp] theorem glue_PQ (x : P) (y : Q) :
    glue d ρ (Sum.inl x) (Sum.inr (Sum.inr y)) = glueCross d ρ x y := rfl
@[simp] theorem glue_FP (z : F) (x : P) :
    glue d ρ (Sum.inr (Sum.inl z)) (Sum.inl x) = d (Sum.inr z) (Sum.inl x) := rfl
@[simp] theorem glue_FF (z z' : F) :
    glue d ρ (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inl z')) = d (Sum.inr z) (Sum.inr z') := rfl
@[simp] theorem glue_FQ (z : F) (y : Q) :
    glue d ρ (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr y)) = ρ (Sum.inl z) (Sum.inr y) := rfl
@[simp] theorem glue_QP (y : Q) (x : P) :
    glue d ρ (Sum.inr (Sum.inr y)) (Sum.inl x) = glueCross d ρ x y := rfl
@[simp] theorem glue_QF (y : Q) (z : F) :
    glue d ρ (Sum.inr (Sum.inr y)) (Sum.inr (Sum.inl z)) = ρ (Sum.inr y) (Sum.inl z) := rfl
@[simp] theorem glue_QQ (y y' : Q) :
    glue d ρ (Sum.inr (Sum.inr y)) (Sum.inr (Sum.inr y')) = ρ (Sum.inr y) (Sum.inr y') := rfl

/-! ### Basic properties of the cross distance -/

theorem glueCross_le_one (x : P) (y : Q) : glueCross d ρ x y ≤ 1 := min_le_left _ _

theorem glueCross_le (x : P) (y : Q) (z : F) :
    glueCross d ρ x y ≤ d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y) :=
  le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ z))

theorem glueCross_nonneg (hd : IsBddPseudo d) (hr : IsBddPseudo ρ) (x : P) (y : Q) :
    0 ≤ glueCross d ρ x y := by
  refine le_min zero_le_one ?_
  refine Finset.le_inf' _ _ ?_
  intro z _
  exact add_nonneg (hd.nonneg _ _) (hr.nonneg _ _)

/-- The inner minimum is attained since `F` is finite: each cross distance is either at the
ceiling `1`, or realized by a point of the gluing locus. -/
theorem glueCross_dichotomy (x : P) (y : Q) :
    glueCross d ρ x y = 1 ∨
      ∃ z : F, glueCross d ρ x y = d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y) := by
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := F))
    (fun z => d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y))
  rw [glueCross, hz]
  rcases le_total (d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y)) 1 with h | h
  · exact Or.inr ⟨z, min_eq_right h⟩
  · exact Or.inl (min_eq_left h)

end

section Triangle

variable {d : P ⊕ F → P ⊕ F → ℝ} {ρ : F ⊕ Q → F ⊕ Q → ℝ}
  (hd : IsBddPseudo d) (hr : IsBddPseudo ρ)
  (hFF : ∀ z z' : F, d (Sum.inr z) (Sum.inr z') = ρ (Sum.inl z) (Sum.inl z'))

include hd hr hFF

/-- Paper Case 1, second inequality: `ω(x,z) ≤ ω(x,y) + ω(y,z)` for `x ∈ P`, `y ∈ Q`,
`z ∈ F`. -/
theorem glue_tri_PQF (x : P) (y : Q) (z : F) :
    d (Sum.inl x) (Sum.inr z) ≤ glueCross d ρ x y + ρ (Sum.inr y) (Sum.inl z) := by
  rcases glueCross_dichotomy d ρ x y with h | ⟨w, h⟩
  · rw [h]
    have := hd.le_one (Sum.inl x) (Sum.inr z)
    have := hr.nonneg (Sum.inr y) (Sum.inl z)
    linarith
  · rw [h]
    have t1 : d (Sum.inl x) (Sum.inr z) ≤
        d (Sum.inl x) (Sum.inr w) + d (Sum.inr w) (Sum.inr z) :=
      hd.triangle _ _ _
    have t2 : ρ (Sum.inl w) (Sum.inl z) ≤
        ρ (Sum.inl w) (Sum.inr y) + ρ (Sum.inr y) (Sum.inl z) := hr.triangle _ _ _
    rw [hFF w z] at t1
    linarith

/-- Paper Case 1, third inequality: `ω(z,y) ≤ ω(z,x) + ω(x,y)` for `z ∈ F`, `x ∈ P`,
`y ∈ Q`. -/
theorem glue_tri_FPQ (z : F) (x : P) (y : Q) :
    ρ (Sum.inl z) (Sum.inr y) ≤ d (Sum.inr z) (Sum.inl x) + glueCross d ρ x y := by
  rcases glueCross_dichotomy d ρ x y with h | ⟨w, h⟩
  · rw [h]
    have := hr.le_one (Sum.inl z) (Sum.inr y)
    have := hd.nonneg (Sum.inr z) (Sum.inl x)
    linarith
  · rw [h]
    have t1 : ρ (Sum.inl z) (Sum.inr y) ≤
        ρ (Sum.inl z) (Sum.inl w) + ρ (Sum.inl w) (Sum.inr y) := hr.triangle _ _ _
    have t2 : d (Sum.inr z) (Sum.inr w) ≤
        d (Sum.inr z) (Sum.inl x) + d (Sum.inl x) (Sum.inr w) := hd.triangle _ _ _
    rw [hFF z w] at t2
    linarith

omit hr hFF in
/-- Paper Case 2, first inequality: `ω(x,y) ≤ ω(x,x') + ω(x',y)` for `x, x' ∈ P`,
`y ∈ Q`. -/
theorem glue_tri_PPQ (x x' : P) (y : Q) :
    glueCross d ρ x y ≤ d (Sum.inl x) (Sum.inl x') + glueCross d ρ x' y := by
  rcases glueCross_dichotomy d ρ x' y with h | ⟨w, h⟩
  · rw [h]
    have := glueCross_le_one d ρ x y
    have := hd.nonneg (Sum.inl x) (Sum.inl x')
    linarith
  · rw [h]
    have t1 := glueCross_le d ρ x y w
    have t2 : d (Sum.inl x) (Sum.inr w) ≤
        d (Sum.inl x) (Sum.inl x') + d (Sum.inl x') (Sum.inr w) := hd.triangle _ _ _
    linarith

/-- Paper Case 2, second inequality: `ω(x,x') ≤ ω(x,y) + ω(x',y)` for `x, x' ∈ P`,
`y ∈ Q`. -/
theorem glue_tri_PQP (x x' : P) (y : Q) :
    d (Sum.inl x) (Sum.inl x') ≤ glueCross d ρ x y + glueCross d ρ x' y := by
  rcases glueCross_dichotomy d ρ x y with h | ⟨w, h⟩
  · rw [h]
    have := hd.le_one (Sum.inl x) (Sum.inl x')
    have := glueCross_nonneg d ρ hd hr x' y
    linarith
  rcases glueCross_dichotomy d ρ x' y with h' | ⟨w', h'⟩
  · rw [h']
    have := hd.le_one (Sum.inl x) (Sum.inl x')
    have := glueCross_nonneg d ρ hd hr x y
    linarith
  rw [h, h']
  have t1 : d (Sum.inl x) (Sum.inl x') ≤
      d (Sum.inl x) (Sum.inr w) + d (Sum.inr w) (Sum.inl x') := hd.triangle _ _ _
  have t2 : d (Sum.inr w) (Sum.inl x') ≤
      d (Sum.inr w) (Sum.inr w') + d (Sum.inr w') (Sum.inl x') := hd.triangle _ _ _
  have t3 : ρ (Sum.inl w) (Sum.inl w') ≤
      ρ (Sum.inl w) (Sum.inr y) + ρ (Sum.inr y) (Sum.inl w') := hr.triangle _ _ _
  have e1 : d (Sum.inr w') (Sum.inl x') = d (Sum.inl x') (Sum.inr w') := hd.symm _ _
  have e2 : ρ (Sum.inr y) (Sum.inl w') = ρ (Sum.inl w') (Sum.inr y) := hr.symm _ _
  rw [hFF w w'] at t2
  linarith

omit hd hFF in
/-- Paper Case 3, first inequality: `ω(x,y) ≤ ω(x,y') + ω(y',y)` for `x ∈ P`,
`y, y' ∈ Q`. -/
theorem glue_tri_PQQ (x : P) (y' y : Q) :
    glueCross d ρ x y ≤ glueCross d ρ x y' + ρ (Sum.inr y') (Sum.inr y) := by
  rcases glueCross_dichotomy d ρ x y' with h | ⟨w, h⟩
  · rw [h]
    have := glueCross_le_one d ρ x y
    have := hr.nonneg (Sum.inr y') (Sum.inr y)
    linarith
  · rw [h]
    have t1 := glueCross_le d ρ x y w
    have t2 : ρ (Sum.inl w) (Sum.inr y) ≤
        ρ (Sum.inl w) (Sum.inr y') + ρ (Sum.inr y') (Sum.inr y) := hr.triangle _ _ _
    linarith

/-- Paper Case 3, second inequality: `ω(y,y') ≤ ω(y,x) + ω(x,y')` for `x ∈ P`,
`y, y' ∈ Q`. -/
theorem glue_tri_QPQ (y y' : Q) (x : P) :
    ρ (Sum.inr y) (Sum.inr y') ≤ glueCross d ρ x y + glueCross d ρ x y' := by
  rcases glueCross_dichotomy d ρ x y with h | ⟨w, h⟩
  · rw [h]
    have := hr.le_one (Sum.inr y) (Sum.inr y')
    have := glueCross_nonneg d ρ hd hr x y'
    linarith
  rcases glueCross_dichotomy d ρ x y' with h' | ⟨w', h'⟩
  · rw [h']
    have := hr.le_one (Sum.inr y) (Sum.inr y')
    have := glueCross_nonneg d ρ hd hr x y
    linarith
  rw [h, h']
  have t1 : ρ (Sum.inr y) (Sum.inr y') ≤
      ρ (Sum.inr y) (Sum.inl w) + ρ (Sum.inl w) (Sum.inr y') := hr.triangle _ _ _
  have t2 : ρ (Sum.inl w) (Sum.inr y') ≤
      ρ (Sum.inl w) (Sum.inl w') + ρ (Sum.inl w') (Sum.inr y') := hr.triangle _ _ _
  have t3 : d (Sum.inr w) (Sum.inr w') ≤
      d (Sum.inr w) (Sum.inl x) + d (Sum.inl x) (Sum.inr w') := hd.triangle _ _ _
  have e1 : ρ (Sum.inr y) (Sum.inl w) = ρ (Sum.inl w) (Sum.inr y) := hr.symm _ _
  have e2 : d (Sum.inr w) (Sum.inl x) = d (Sum.inl x) (Sum.inr w) := hd.symm _ _
  rw [hFF w w'] at t3
  linarith

/-- Paper Lemma 3.1: the amalgam is a bounded-by-one pseudometric. -/
theorem glue_isBddPseudo : IsBddPseudo (glue d ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (x | (z | y)) (x' | (z' | y')) <;>
      simp only [glue_PP, glue_PF, glue_PQ, glue_FP, glue_FF, glue_FQ, glue_QP, glue_QF,
        glue_QQ] <;>
      first
        | exact hd.nonneg _ _
        | exact hr.nonneg _ _
        | exact glueCross_nonneg d ρ hd hr _ _
  · rintro (x | (z | y)) (x' | (z' | y')) <;>
      simp only [glue_PP, glue_PF, glue_PQ, glue_FP, glue_FF, glue_FQ, glue_QP, glue_QF,
        glue_QQ] <;>
      first
        | exact hd.le_one _ _
        | exact hr.le_one _ _
        | exact glueCross_le_one d ρ _ _
  · rintro (x | (z | y)) <;>
      simp only [glue_PP, glue_FF, glue_QQ] <;>
      first
        | exact hd.diag _
        | exact hr.diag _
  · rintro (x | (z | y)) (x' | (z' | y')) <;>
      simp only [glue_PP, glue_PF, glue_PQ, glue_FP, glue_FF, glue_FQ, glue_QP, glue_QF,
        glue_QQ] <;>
      first
        | rfl
        | exact hd.symm _ _
        | exact hr.symm _ _
  · rintro (x | (z | y)) (x' | (z' | y')) (x'' | (z'' | y'')) <;>
      simp only [glue_PP, glue_PF, glue_PQ, glue_FP, glue_FF, glue_FQ, glue_QP, glue_QF,
        glue_QQ]
    -- (P, P, ·)
    · exact hd.triangle _ _ _
    · exact hd.triangle _ _ _
    · exact glue_tri_PPQ hd _ _ _
    -- (P, F, ·)
    · exact hd.triangle _ _ _
    · exact hd.triangle _ _ _
    · exact glueCross_le d ρ _ _ _
    -- (P, Q, ·)
    · exact glue_tri_PQP hd hr hFF _ _ _
    · exact glue_tri_PQF hd hr hFF _ _ _
    · exact glue_tri_PQQ hr _ _ _
    -- (F, P, ·)
    · exact hd.triangle _ _ _
    · exact hd.triangle _ _ _
    · exact glue_tri_FPQ hd hr hFF _ _ _
    -- (F, F, ·)
    · exact hd.triangle _ _ _
    · exact hd.triangle _ _ _
    · rw [hFF]; exact hr.triangle _ _ _
    -- (F, Q, ·)
    · have h := glue_tri_PQF hd hr hFF x'' y' z
      rw [hd.symm (Sum.inr z) (Sum.inl x''), hr.symm (Sum.inl z) (Sum.inr y')]
      linarith
    · rw [hFF]; exact hr.triangle _ _ _
    · exact hr.triangle _ _ _
    -- (Q, P, ·)
    · linarith [glue_tri_PPQ (ρ := ρ) hd x'' x' y, hd.symm (Sum.inl x'') (Sum.inl x')]
    · linarith [glue_tri_FPQ hd hr hFF z'' x' y, hr.symm (Sum.inr y) (Sum.inl z''),
        hd.symm (Sum.inr z'') (Sum.inl x')]
    · exact glue_tri_QPQ hd hr hFF _ _ _
    -- (Q, F, ·)
    · linarith [glueCross_le d ρ x'' y z', hr.symm (Sum.inr y) (Sum.inl z'),
        hd.symm (Sum.inr z') (Sum.inl x'')]
    · rw [hFF]; exact hr.triangle _ _ _
    · exact hr.triangle _ _ _
    -- (Q, Q, ·)
    · linarith [glue_tri_PQQ (d := d) hr x'' y' y, hr.symm (Sum.inr y') (Sum.inr y)]
    · exact hr.triangle _ _ _
    · exact hr.triangle _ _ _

end Triangle

/-- Paper Lemma 3.1, the dichotomy: every new distance is either at the ceiling `1`, or
lies on a geodesic through the gluing locus `F`. -/
theorem glue_dichotomy (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) (x : P) (y : Q) :
    glue d ρ (Sum.inl x) (Sum.inr (Sum.inr y)) = 1 ∨
      ∃ z : F, glue d ρ (Sum.inl x) (Sum.inr (Sum.inr y)) =
        glue d ρ (Sum.inl x) (Sum.inr (Sum.inl z)) +
          glue d ρ (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr y)) := by
  simpa using glueCross_dichotomy d ρ x y
