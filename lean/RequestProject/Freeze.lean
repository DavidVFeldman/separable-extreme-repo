import RequestProject.GlueFamily
import RequestProject.Transport

/-!
# Stage 2 of the Tier 4 construction: freezing a countable family of pairs

Given a bounded-by-one pseudometric space `(W, D)` and a family of pairs
`e j : Bool → W` such that the distance of each pair is realized inside some *finite rigid*
metric, we glue in one copy of that finite metric for every pair, all at once, and obtain a
bounded-by-one pseudometric `D'` on `W ⊕ (J × ℕ)` with:

* `D'` restricted to `W` is `D`;
* every perturbation of `D'` vanishes on each designated pair;
* a perturbation of `D'` vanishing on all of `W` vanishes identically.

The new points of the piece attached to the pair `j` are indexed by `ℕ` rather than by the
finite carrier itself: a surjection `ℕ → F j` is used, which keeps the family of pieces free
of dependent types. Rigidity survives this pullback (`Rigid.comp_surjective`).
-/

set_option autoImplicit false

open scoped BigOperators

/-- Piece data coming from positions on the real line: distances inside a piece and to its
locus are given by `|·-·|` of positions in `[0,1]`. -/
theorem isPieceData_of_real {X Y I L : Type*} (d : X → X → ℝ) (idx : Y → I) (g : I → L → X)
    (P : Y → ℝ) (Q : I → L → ℝ)
    (hP0 : ∀ y, 0 ≤ P y) (hP1 : ∀ y, P y ≤ 1) (hQ0 : ∀ i l, 0 ≤ Q i l) (hQ1 : ∀ i l, Q i l ≤ 1)
    (hgd : ∀ i l l', d (g i l) (g i l') = |Q i l - Q i l'|) :
    IsPieceData d idx g (fun y y' => |P y - P y'|) (fun y l => |P y - Q (idx y) l|) where
  r_nonneg y y' := abs_nonneg _
  r_le_one y y' := by
    rw [abs_le]; constructor <;> [linarith [hP0 y, hP1 y']; linarith [hP0 y', hP1 y]]
  r_diag y := by simp
  r_symm y y' := abs_sub_comm _ _
  s_nonneg y l := abs_nonneg _
  s_le_one y l := by
    rw [abs_le]
    constructor <;> [linarith [hP0 y, hQ1 (idx y) l]; linarith [hP1 y, hQ0 (idx y) l]]
  tri_rrr y y' y'' _ _ := abs_sub_le _ _ _
  tri_rrs y y' l h := by rw [h]; exact abs_sub_le _ _ _
  tri_ssr y y' l h := by
    have e : |P y' - Q (idx y') l| = |Q (idx y) l - P y'| := by rw [h, abs_sub_comm]
    rw [e]
    exact abs_sub_le _ _ _
  tri_ssd y l l' := by
    rw [hgd]
    exact abs_sub_le _ _ _
  tri_dss y l l' := by
    rw [hgd]
    have e : |P y - Q (idx y) l| = |Q (idx y) l - P y| := abs_sub_comm _ _
    rw [e]
    exact abs_sub_le _ _ _

/-- **Stage 2.** Freezing a family of pairs by gluing in finite rigid metrics. -/
theorem exists_freezing_extension {W J : Type*} (D : W → W → ℝ) (hD : IsBddPseudo D)
    (e : J → Bool → W)
    (hfreeze : ∀ j : J, ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
        IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = D (e j false) (e j true)) :
    ∃ D' : (W ⊕ J × ℕ) → (W ⊕ J × ℕ) → ℝ,
      IsBddPseudo D' ∧
      (∀ w w', D' (Sum.inl w) (Sum.inl w') = D w w') ∧
      (∀ E, IsPerturbation D' E →
        (∀ j, E (Sum.inl (e j false)) (Sum.inl (e j true)) = 0) ∧
        ((∀ w w', E (Sum.inl w) (Sum.inl w') = 0) → ∀ a b, E a b = 0)) := by
  classical
  choose F instF rho uu vv hbdd hrig hval using hfreeze
  have hsurj : ∀ j, ∃ f : ℕ → F j, Function.Surjective f := by
    intro j
    haveI := instF j
    haveI : Nonempty (F j) := ⟨uu j⟩
    exact exists_surjective_nat (F j)
  choose pi hpi using hsurj
  set uv : ∀ j : J, Bool → F j := fun j b => if b then vv j else uu j with huv
  set r₂ : (J × ℕ) → (J × ℕ) → ℝ :=
    fun y y' => if h : y.1 = y'.1 then rho y.1 (pi y.1 y.2) (pi y.1 y'.2) else 0 with hr₂
  set s₂ : (J × ℕ) → Bool → ℝ := fun y b => rho y.1 (pi y.1 y.2) (uv y.1 b) with hs₂
  -- the pieces agree with `D` on their loci
  have hcompat : ∀ (j : J) (b b' : Bool), D (e j b) (e j b') = rho j (uv j b) (uv j b') := by
    intro j b b'
    cases b <;> cases b'
    · rw [hD.diag, huv]; simp [(hbdd j).diag]
    · rw [huv]; simpa using (hval j).symm
    · rw [hD.symm, huv]
      simp only [if_neg (by simp : ¬ (false = true))]
      rw [(hbdd j).symm]
      simpa using (hval j).symm
    · rw [hD.diag, huv]; simp [(hbdd j).diag]
  have hp : IsPieceData D (Prod.fst : J × ℕ → J) e r₂ s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y y'
      simp only [hr₂]
      split
      · exact (hbdd _).nonneg _ _
      · exact le_rfl
    · intro y y'
      simp only [hr₂]
      split
      · exact (hbdd _).le_one _ _
      · exact zero_le_one
    · intro y
      simp only [hr₂, dif_pos]
      exact (hbdd _).diag _
    · rintro ⟨j, n⟩ ⟨j', n'⟩
      by_cases h : j = j'
      · subst h
        simp only [hr₂, dif_pos rfl]
        exact (hbdd j).symm _ _
      · simp only [hr₂, dif_neg h, dif_neg (Ne.symm h)]
    · intro y b; exact (hbdd _).nonneg _ _
    · intro y b; exact (hbdd _).le_one _ _
    · rintro ⟨j, n⟩ ⟨j', n'⟩ ⟨j'', n''⟩ h1 h2
      simp only at h1 h2
      subst h1; subst h2
      simp only [hr₂, dif_pos rfl]
      exact (hbdd j).triangle _ _ _
    · rintro ⟨j, n⟩ ⟨j', n'⟩ l h
      simp only at h
      subst h
      simp only [hr₂, hs₂, dif_pos rfl]
      exact (hbdd j).triangle _ _ _
    · rintro ⟨j, n⟩ ⟨j', n'⟩ l h
      simp only at h
      subst h
      simp only [hr₂, hs₂, dif_pos rfl]
      have h1 := (hbdd j).triangle (pi j n) (uv j l) (pi j n')
      have h2 := (hbdd j).symm (uv j l) (pi j n')
      linarith
    · rintro ⟨j, n⟩ l l'
      simp only [hs₂]
      rw [hcompat]
      have h1 := (hbdd j).triangle (pi j n) (uv j l') (uv j l)
      exact h1
    · rintro ⟨j, n⟩ l l'
      simp only [hs₂]
      rw [hcompat]
      have h1 := (hbdd j).triangle (uv j l) (pi j n) (uv j l')
      have h2 := (hbdd j).symm (uv j l) (pi j n)
      linarith
  refine ⟨glueFamily D (Prod.fst : J × ℕ → J) e r₂ s₂, glueFamily_isBddPseudo hD hp,
    fun w w' => rfl, ?_⟩
  intro E hE
  set D' := glueFamily D (Prod.fst : J × ℕ → J) e r₂ s₂ with hD'
  have hD'p : IsBddPseudo D' := glueFamily_isBddPseudo hD hp
  -- the map placing the finite piece `j` inside the amalgam
  set Phi : J → (ℕ ⊕ Bool) → (W ⊕ J × ℕ) :=
    fun j => Sum.elim (fun n => Sum.inr (j, n)) (fun b => Sum.inl (e j b)) with hPhi
  set theta : ∀ j : J, (ℕ ⊕ Bool) → F j := fun j => Sum.elim (pi j) (uv j) with htheta
  have hthetasurj : ∀ j, Function.Surjective (theta j) := by
    intro j x
    obtain ⟨n, hn⟩ := hpi j x
    exact ⟨Sum.inl n, by simpa [htheta] using hn⟩
  have hiso : ∀ (j : J) (a b : ℕ ⊕ Bool),
      D' (Phi j a) (Phi j b) = rho j (theta j a) (theta j b) := by
    intro j a b
    have hloc : ∀ (n : ℕ) (c : Bool),
        D' (Sum.inl (e j c)) (Sum.inr (j, n)) = rho j (pi j n) (uv j c) := by
      intro n c
      have := glueFamily_restrict_locus (d := D) (idx := (Prod.fst : J × ℕ → J)) (g := e)
        (r := r₂) (s := s₂) hD hp (j, n) c
      simpa [hD', hs₂] using this
    cases a with
    | inl n =>
        cases b with
        | inl m =>
            have := glueFamily_restrict_piece (d := D) (idx := (Prod.fst : J × ℕ → J))
              (g := e) (r := r₂) (s := s₂) (y := (j, n)) (y' := (j, m)) rfl
            simpa [hD', hPhi, htheta, hr₂] using this
        | inr c =>
            have h1 : D' (Phi j (Sum.inl n)) (Phi j (Sum.inr c)) =
                D' (Sum.inl (e j c)) (Sum.inr (j, n)) := by
              simp only [hPhi, Sum.elim_inl, Sum.elim_inr]
              exact hD'p.symm _ _
            rw [h1, hloc]
            simp [htheta]
    | inr c =>
        cases b with
        | inl m =>
            have h1 : D' (Phi j (Sum.inr c)) (Phi j (Sum.inl m)) =
                D' (Sum.inl (e j c)) (Sum.inr (j, m)) := by
              simp only [hPhi, Sum.elim_inl, Sum.elim_inr]
            rw [h1, hloc]
            simp [htheta, (hbdd j).symm]
        | inr c' =>
            simp only [hPhi, Sum.elim_inr, htheta]
            show D (e j c) (e j c') = rho j (uv j c) (uv j c')
            exact hcompat j c c'
  -- a perturbation vanishes on each glued piece, locus included
  have hpiece : ∀ (j : J) (a b : ℕ ⊕ Bool), E (Phi j a) (Phi j b) = 0 := by
    intro j
    exact pert_eq_zero_of_isometry hE ((hrig j).comp_surjective (hthetasurj j)) (Phi j)
      (hiso j)
  refine ⟨fun j => ?_, ?_⟩
  · have := hpiece j (Sum.inr false) (Sum.inr true)
    simpa [hPhi] using this
  · intro hbase
    -- first: cross pairs base–piece
    have hcross : ∀ (w : W) (y : J × ℕ), E (Sum.inl w) (Sum.inr y) = 0 := by
      rintro w ⟨j, n⟩
      rcases glueFamily_dichotomy_base_piece (d := D) (idx := (Prod.fst : J × ℕ → J))
        (g := e) (r := r₂) (s := s₂) hD hp w (j, n) with h1 | ⟨l, h1⟩
      · exact pert_eq_zero_of_dist_eq_one hE h1
      · have htight : D' (Sum.inl w) (Sum.inr (j, n)) =
            D' (Sum.inl w) (Sum.inl (e j l)) + D' (Sum.inl (e j l)) (Sum.inr (j, n)) := h1
        rw [pert_add_of_tight D' E hE htight, hbase]
        have := hpiece j (Sum.inr l) (Sum.inl n)
        simp only [hPhi, Sum.elim_inl, Sum.elim_inr] at this
        rw [this, add_zero]
    rintro (w | ⟨j, n⟩) (w' | ⟨j', n'⟩)
    · exact hbase w w'
    · exact hcross w (j', n')
    · rw [hE.1]; exact hcross w' (j, n)
    · by_cases hjj : j = j'
      · subst hjj
        have := hpiece j (Sum.inl n) (Sum.inl n')
        simpa [hPhi] using this
      · rcases glueFamily_dichotomy_piece_piece (d := D) (idx := (Prod.fst : J × ℕ → J))
          (g := e) (r := r₂) (s := s₂) hD hp (y := (j, n)) (y' := (j', n')) hjj with
          h1 | ⟨l, l', h1⟩
        · exact pert_eq_zero_of_dist_eq_one hE h1
        · -- a tight three-link chain through the two loci
          set p : ℕ → (W ⊕ J × ℕ) := fun k =>
            match k with
            | 0 => Sum.inr (j, n)
            | 1 => Sum.inl (e j l)
            | 2 => Sum.inl (e j' l')
            | _ => Sum.inr (j', n') with hpdef
          have htight : D' (p 0) (p 3) = ∑ i ∈ Finset.range 3, D' (p i) (p (i + 1)) := by
            simp only [hpdef, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
            simpa using h1
          have hsum := pert_add_of_tight_chain D' E hE (m := 3) p htight
          have h0 : E (p 0) (p 1) = 0 := by
            have := hpiece j (Sum.inl n) (Sum.inr l)
            simpa [hpdef, hPhi] using this
          have h1' : E (p 1) (p 2) = 0 := by
            simpa [hpdef] using hbase (e j l) (e j' l')
          have h2 : E (p 2) (p 3) = 0 := by
            have := hpiece j' (Sum.inr l') (Sum.inl n')
            simpa [hpdef, hPhi] using this
          have : E (p 0) (p 3) = 0 := by
            rw [hsum]
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
            rw [h0, h1', h2]
            ring
          simpa [hpdef] using this
