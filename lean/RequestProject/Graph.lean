import RequestProject.Functor
import RequestProject.Isolation

/-!
# Tier 6d: the graph reduction

The metric content of §7 of the paper. To a graph `G` on `ℕ` we attach the *graph space*
`X_G`: the carrier is `ℕ`, and two distinct points are at distance `1/√3` if they are
adjacent and `1/√5` if they are not. Both values are irrational and lie in `(1/3, 2/3)`, so
`X_G` is a bounded-by-one pseudometric space (indeed a metric space) all of whose distances
between distinct points are irrational.

`graphSpace_iso_iff` says that isomorphism of graphs is the same as isometry of the graph
spaces, and `main_equivalence` — the paper's Theorem 7.6 minus the word "Borel" — says that
it is the same as isometry of the canonical extensions `E(X_G)`, which are extreme points by
`E_rigid`.

**Hypotheses added to the commission's shape.** `graphSpace_iso_iff` is stated for *simple*
graphs: `G` and `H` symmetric and irreflexive. Both hypotheses are necessary, and the
theorems `graphSpace_iso_iff_needs_symmetry` and `graphSpace_iso_iff_needs_irreflexive`
below refute the statement without them: the graph space only sees the symmetrized
adjacency relation, and never sees loops.
-/

set_option autoImplicit false

namespace Canonical

open Classical in
/-- **The graph space of `G`**: distinct points are at distance `1/√3` when adjacent and
`1/√5` when not. -/
noncomputable def graphSpace (G : ℕ → ℕ → Prop) : ℕ → ℕ → ℝ :=
  fun m n => if m = n then 0 else if G m n ∨ G n m then (Real.sqrt 3)⁻¹ else (Real.sqrt 5)⁻¹

variable {G H : ℕ → ℕ → Prop}

theorem sqrt3_inv_lt : (Real.sqrt 3)⁻¹ < 2 / 3 := by
  have h3 : (3 : ℝ) / 2 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]
  have h0 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [inv_lt_comm₀ h0 (by norm_num)]
  linarith

theorem lt_sqrt3_inv : (1 : ℝ) / 3 < (Real.sqrt 3)⁻¹ := by
  have h3 : Real.sqrt 3 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]
  have h0 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [lt_inv_comm₀ (by norm_num) h0]
  linarith

theorem sqrt5_inv_lt : (Real.sqrt 5)⁻¹ < 2 / 3 := by
  have h5 : (3 : ℝ) / 2 < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0), Real.sqrt_nonneg 5]
  have h0 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [inv_lt_comm₀ h0 (by norm_num)]
  linarith

theorem lt_sqrt5_inv : (1 : ℝ) / 3 < (Real.sqrt 5)⁻¹ := by
  have h5 : Real.sqrt 5 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0), Real.sqrt_nonneg 5]
  have h0 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [lt_inv_comm₀ (by norm_num) h0]
  linarith

theorem sqrt3_inv_irrational : Irrational ((Real.sqrt 3)⁻¹) :=
  (Nat.prime_three.irrational_sqrt).inv

theorem sqrt5_inv_irrational : Irrational ((Real.sqrt 5)⁻¹) :=
  ((by norm_num : Nat.Prime 5).irrational_sqrt).inv

theorem sqrt3_inv_ne_sqrt5_inv : (Real.sqrt 3)⁻¹ ≠ (Real.sqrt 5)⁻¹ := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 3 < Real.sqrt 5 := by
    apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have : (Real.sqrt 5)⁻¹ < (Real.sqrt 3)⁻¹ := by
    exact inv_strictAnti₀ h3 hlt
  exact ne_of_gt this

@[simp] theorem graphSpace_diag (n : ℕ) : graphSpace G n n = 0 := by
  simp [graphSpace]

/-- The two values taken by the graph space on distinct points. -/
theorem graphSpace_of_ne {m n : ℕ} (h : m ≠ n) :
    graphSpace G m n = (Real.sqrt 3)⁻¹ ∨ graphSpace G m n = (Real.sqrt 5)⁻¹ := by
  classical
  simp only [graphSpace, if_neg h]
  by_cases hadj : G m n ∨ G n m
  · exact Or.inl (if_pos hadj)
  · exact Or.inr (if_neg hadj)

theorem graphSpace_bounds (m n : ℕ) :
    graphSpace G m n = 0 ∨ ((1 : ℝ) / 3 < graphSpace G m n ∧ graphSpace G m n < 2 / 3) := by
  by_cases h : m = n
  · subst h; exact Or.inl (graphSpace_diag _)
  · rcases graphSpace_of_ne (G := G) h with hv | hv <;> rw [hv]
    · exact Or.inr ⟨lt_sqrt3_inv, sqrt3_inv_lt⟩
    · exact Or.inr ⟨lt_sqrt5_inv, sqrt5_inv_lt⟩

theorem graphSpace_symm (m n : ℕ) : graphSpace G m n = graphSpace G n m := by
  classical
  by_cases h : m = n
  · subst h; rfl
  · simp only [graphSpace, if_neg h, if_neg (Ne.symm h)]
    by_cases hadj : G m n ∨ G n m
    · rw [if_pos hadj, if_pos (Or.symm hadj)]
    · rw [if_neg hadj, if_neg (fun hc => hadj (Or.symm hc))]

/-- **The graph space is a bounded-by-one pseudometric space.** -/
theorem graphSpace_isBddPseudo : IsBddPseudo (graphSpace G) where
  nonneg m n := by
    rcases graphSpace_bounds (G := G) m n with h | h
    · rw [h]
    · linarith [h.1]
  le_one m n := by
    rcases graphSpace_bounds (G := G) m n with h | h
    · rw [h]; norm_num
    · linarith [h.2]
  diag n := graphSpace_diag n
  symm m n := graphSpace_symm m n
  triangle m n k := by
    by_cases hmk : m = k
    · subst hmk
      rw [graphSpace_diag]
      rcases graphSpace_bounds (G := G) m n with h | h
      · rw [h, graphSpace_symm, h]; norm_num
      · have h2 : graphSpace G n m = graphSpace G m n := graphSpace_symm n m
        rw [h2]; linarith [h.1]
    · by_cases hmn : m = n
      · subst hmn; rw [graphSpace_diag, zero_add]
      · by_cases hnk : n = k
        · subst hnk; rw [graphSpace_diag, add_zero]
        · rcases graphSpace_bounds (G := G) m n with h1 | h1
          · exact absurd (by
              rcases graphSpace_of_ne (G := G) hmn with hv | hv <;> rw [hv] at h1
              · exact absurd h1.symm (ne_of_gt (by linarith [lt_sqrt3_inv]))
              · exact absurd h1.symm (ne_of_gt (by linarith [lt_sqrt5_inv]))) (fun h => h)
          · rcases graphSpace_bounds (G := G) n k with h2 | h2
            · exact absurd (by
                rcases graphSpace_of_ne (G := G) hnk with hv | hv <;> rw [hv] at h2
                · exact absurd h2.symm (ne_of_gt (by linarith [lt_sqrt3_inv]))
                · exact absurd h2.symm (ne_of_gt (by linarith [lt_sqrt5_inv]))) (fun h => h)
            · rcases graphSpace_bounds (G := G) m k with h3 | h3
              · rw [h3]; linarith [h1.1, h2.1]
              · linarith [h1.1, h2.1, h3.2]

/-- Every point of a graph space has a partner at irrational distance. -/
theorem graphSpace_irrational {m n : ℕ} (h : m ≠ n) : Irrational (graphSpace G m n) := by
  rcases graphSpace_of_ne (G := G) h with hv | hv <;> rw [hv]
  · exact sqrt3_inv_irrational
  · exact sqrt5_inv_irrational

theorem graphSpace_hirr : ∀ n : ℕ, ∃ n', Irrational (graphSpace G n n') :=
  fun n => ⟨n + 1, graphSpace_irrational (by omega)⟩

/-! ### Graph isomorphism is isometry of the graph spaces -/

/-- **Isomorphism of simple graphs is isometry of their graph spaces.** -/
theorem graphSpace_iso_iff (hG : Symmetric G) (hGi : ∀ n, ¬ G n n) (hH : Symmetric H)
    (hHi : ∀ n, ¬ H n n) :
    (∃ σ : ℕ ≃ ℕ, ∀ m n, (G m n ↔ H (σ m) (σ n))) ↔
      (∃ φ : ℕ ≃ ℕ, ∀ m n, graphSpace H (φ m) (φ n) = graphSpace G m n) := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun m n => ?_⟩
    by_cases h : m = n
    · subst h; simp
    · have h' : σ m ≠ σ n := fun hc => h (σ.injective hc)
      simp only [graphSpace, if_neg h, if_neg h']
      by_cases hadj : G m n ∨ G n m
      · have hadj' : H (σ m) (σ n) ∨ H (σ n) (σ m) := by
          rcases hadj with ha | ha
          · exact Or.inl ((hσ m n).mp ha)
          · exact Or.inr ((hσ n m).mp ha)
        rw [if_pos hadj, if_pos hadj']
      · have hadj' : ¬ (H (σ m) (σ n) ∨ H (σ n) (σ m)) := by
          rintro (hc | hc)
          · exact hadj (Or.inl ((hσ m n).mpr hc))
          · exact hadj (Or.inr ((hσ n m).mpr hc))
        rw [if_neg hadj, if_neg hadj']
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun m n => ?_⟩
    by_cases h : m = n
    · subst h
      constructor
      · intro hc; exact absurd hc (hGi m)
      · intro hc; exact absurd hc (hHi (φ m))
    · have h' : φ m ≠ φ n := fun hc => h (φ.injective hc)
      have hv := hφ m n
      simp only [graphSpace, if_neg h, if_neg h'] at hv
      constructor
      · intro hg
        by_contra hc
        have hnadj : ¬ (H (φ m) (φ n) ∨ H (φ n) (φ m)) := by
          rintro (hx | hx)
          · exact hc hx
          · exact hc (hH hx)
        rw [if_neg hnadj, if_pos (Or.inl hg)] at hv
        exact sqrt3_inv_ne_sqrt5_inv hv.symm
      · intro hh
        by_contra hc
        have hnadj : ¬ (G m n ∨ G n m) := by
          rintro (hx | hx)
          · exact hc hx
          · exact hc (hG hx)
        rw [if_pos (Or.inl hh), if_neg hnadj] at hv
        exact sqrt3_inv_ne_sqrt5_inv hv

/-- **The symmetry hypothesis of `graphSpace_iso_iff` cannot be dropped**: the graph space
only sees the symmetrized adjacency relation. -/
theorem graphSpace_iso_iff_needs_symmetry :
    ¬ (∀ G H : ℕ → ℕ → Prop,
        (∃ σ : ℕ ≃ ℕ, ∀ m n, (G m n ↔ H (σ m) (σ n))) ↔
          (∃ φ : ℕ ≃ ℕ, ∀ m n, graphSpace H (φ m) (φ n) = graphSpace G m n)) := by
  classical
  intro hcon
  set G : ℕ → ℕ → Prop := fun m n => m = 0 ∧ n = 1 with hGdef
  set H : ℕ → ℕ → Prop := fun m n => (m = 0 ∧ n = 1) ∨ (m = 1 ∧ n = 0) with hHdef
  have hval : ∀ m n, graphSpace H m n = graphSpace G m n := by
    intro m n
    by_cases h : m = n
    · subst h; simp
    · simp only [graphSpace, if_neg h, hGdef, hHdef]
      by_cases hadj : (m = 0 ∧ n = 1) ∨ (n = 0 ∧ m = 1)
      · rw [if_pos (by tauto), if_pos hadj]
      · rw [if_neg (by tauto), if_neg hadj]
  obtain ⟨σ, hσ⟩ := (hcon G H).mpr ⟨Equiv.refl ℕ, fun m n => hval m n⟩
  have h1 : H (σ 0) (σ 1) := (hσ 0 1).mp ⟨rfl, rfl⟩
  have h2 : ¬ G 1 0 := by simp [hGdef]
  refine h2 ((hσ 1 0).mpr ?_)
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inr ⟨hb, ha⟩
  · exact Or.inl ⟨hb, ha⟩

/-- **The irreflexivity hypothesis of `graphSpace_iso_iff` cannot be dropped**: the graph
space never sees loops. -/
theorem graphSpace_iso_iff_needs_irreflexive :
    ¬ (∀ G H : ℕ → ℕ → Prop,
        (∃ σ : ℕ ≃ ℕ, ∀ m n, (G m n ↔ H (σ m) (σ n))) ↔
          (∃ φ : ℕ ≃ ℕ, ∀ m n, graphSpace H (φ m) (φ n) = graphSpace G m n)) := by
  classical
  intro hcon
  set G : ℕ → ℕ → Prop := fun m n => m = 0 ∧ n = 0 with hGdef
  set H : ℕ → ℕ → Prop := fun _ _ => False with hHdef
  have hval : ∀ m n, graphSpace H m n = graphSpace G m n := by
    intro m n
    by_cases h : m = n
    · subst h; simp
    · simp only [graphSpace, if_neg h, hGdef, hHdef]
      rw [if_neg (by tauto), if_neg (by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact h rfl)]
  obtain ⟨σ, hσ⟩ := (hcon G H).mpr ⟨Equiv.refl ℕ, fun m n => hval m n⟩
  exact (hσ 0 0).mp ⟨rfl, rfl⟩

/-! ### The main equivalence -/

/-- **The main equivalence** (the paper's Theorem `thm:gi` minus the word "Borel"): two simple
graphs are isomorphic if and only if the canonical extensions of their graph spaces — which
are extreme points of the convex set of bounded-by-one pseudometrics, by `E_rigid` — are
isometric. -/
theorem main_equivalence (hG : Symmetric G) (hGi : ∀ n, ¬ G n n) (hH : Symmetric H)
    (hHi : ∀ n, ¬ H n n) :
    (∃ σ : ℕ ≃ ℕ, ∀ m n, (G m n ↔ H (σ m) (σ n))) ↔
      (∃ Φ : ECarrier ℕ (graphSpace G) ≃ ECarrier ℕ (graphSpace H),
        ∀ x y, EDist (graphSpace H) (Φ x) (Φ y) = EDist (graphSpace G) x y) := by
  constructor
  · intro hiso
    obtain ⟨φ, hφ⟩ := (graphSpace_iso_iff hG hGi hH hHi).mp hiso
    obtain ⟨Ψ, hΨbij, -, hΨiso⟩ :=
      E_functor_surj (dA := graphSpace G) (dB := graphSpace H) φ hφ φ.bijective
    exact ⟨Equiv.ofBijective Ψ hΨbij, fun x y => hΨiso x y⟩
  · rintro ⟨Φ, hΦ⟩
    obtain ⟨φ, hφbij, hφiso, -⟩ :=
      recovery (dA := graphSpace G) (dB := graphSpace H) graphSpace_isBddPseudo
        graphSpace_isBddPseudo graphSpace_hirr graphSpace_hirr Φ Φ.bijective hΦ
    exact (graphSpace_iso_iff hG hGi hH hHi).mpr
      ⟨Equiv.ofBijective φ hφbij, fun m n => hφiso m n⟩

end Canonical
