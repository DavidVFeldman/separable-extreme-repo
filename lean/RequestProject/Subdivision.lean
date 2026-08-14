import RequestProject.Freeze
import RequestProject.Subdivide

/-!
# Stage 1 of the Tier 4 construction: subdividing a family of pairs

Every target pair `(tu p, tv p)` of positive distance is subdivided at once: a countable
chain of new points is glued along the two-point locus `{tu p, tv p}`, sitting at the
partial sums of a sequence of positive rationals adding up to the distance of the pair
(paper Lemma 4.1, here for a whole family).

The output records the chain `c p : ℕ → X ⊕ T × ℕ`, the gaps `a p i : ℚ`, and the fact that
a perturbation of the amalgam which vanishes on the base and on every gap vanishes
identically.
-/

set_option autoImplicit false

open scoped BigOperators

/-- **Stage 1.** Subdividing a family of pairs into countable chains of rational gaps. -/
theorem exists_subdivision_extension {X T : Type*} (d : X → X → ℝ) (hd : IsBddPseudo d)
    (tu tv : T → X) (hpos : ∀ p, 0 < d (tu p) (tv p)) :
    ∃ (ω : (X ⊕ T × ℕ) → (X ⊕ T × ℕ) → ℝ) (a : T → ℕ → ℚ) (c : T → ℕ → (X ⊕ T × ℕ)),
      IsBddPseudo ω ∧
      (∀ x x', ω (Sum.inl x) (Sum.inl x') = d x x') ∧
      (∀ p, c p 0 = Sum.inl (tu p)) ∧
      (∀ p i, 0 < a p i) ∧ (∀ p i, (a p i : ℝ) ≤ 1) ∧
      (∀ p i, ω (c p i) (c p (i + 1)) = (a p i : ℝ)) ∧
      (∀ p j, ω (c p 0) (c p j) = ∑ i ∈ Finset.range j, (a p i : ℝ)) ∧
      (∀ p j, ω (c p j) (Sum.inl (tv p)) =
        d (tu p) (tv p) - ∑ i ∈ Finset.range j, (a p i : ℝ)) ∧
      (∀ p, HasSum (fun i => (a p i : ℝ)) (d (tu p) (tv p))) ∧
      (∀ E, IsPerturbation ω E → (∀ p i, E (c p i) (c p (i + 1)) = 0) →
        (∀ x x', E (Sum.inl x) (Sum.inl x') = 0) → ∀ w w', E w w' = 0) := by
  classical
  choose a hapos hasum using fun p => exists_rat_seq_hasSum (hpos p)
  set t : T → ℝ := fun p => d (tu p) (tv p) with ht
  set pos : T → ℕ → ℝ := fun p j => ∑ i ∈ Finset.range j, (a p i : ℝ) with hposdef
  have hane : ∀ p i, (0:ℝ) < (a p i : ℝ) := fun p i => by exact_mod_cast hapos p i
  have htp : ∀ p, t p = d (tu p) (tv p) := fun p => rfl
  have hposv : ∀ p j, pos p j = ∑ i ∈ Finset.range j, (a p i : ℝ) := fun p j => rfl
  have hpos0 : ∀ p, pos p 0 = 0 := fun p => by simp [hposv]
  have hposnn : ∀ p j, 0 ≤ pos p j :=
    fun p j => Finset.sum_nonneg fun i _ => (hane p i).le
  have hpossucc : ∀ p j, pos p (j + 1) = pos p j + (a p j : ℝ) := by
    intro p j; simp [hposdef, Finset.sum_range_succ]
  have hposlt : ∀ p j, pos p j < t p := by
    intro p j
    have h1 : pos p (j + 1) ≤ t p :=
      sum_le_hasSum (Finset.range (j + 1)) (fun i _ => (hane p i).le) (hasum p)
    have := hpossucc p j
    have := hane p j
    linarith
  have hseg : ∀ p j m, pos p (j + m) - pos p j = ∑ i ∈ Finset.range m, (a p (j + i) : ℝ) := by
    intro p j m
    induction m with
    | zero => simp
    | succ m ih =>
        have e : pos p (j + (m + 1)) = pos p (j + m) + (a p (j + m) : ℝ) := by
          have hjm : j + (m + 1) = (j + m) + 1 := by omega
          rw [hjm, hpossucc]
        rw [e, Finset.sum_range_succ, ← ih]; ring
  have hposmono : ∀ p j k, j ≤ k → pos p j ≤ pos p k := by
    intro p j k hjk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have := hseg p j m
    have hnn : (0:ℝ) ≤ ∑ i ∈ Finset.range m, (a p (j + i) : ℝ) :=
      Finset.sum_nonneg fun i _ => (hane p (j + i)).le
    linarith
  have ht1 : ∀ p, t p ≤ 1 := fun p => hd.le_one _ _
  -- the piece data
  set gl : T → Bool → X := fun p b => if b then tv p else tu p with hgl
  set Q : T → Bool → ℝ := fun p b => if b then t p else 0 with hQ
  set P : (T × ℕ) → ℝ := fun y => pos y.1 (y.2 + 1) with hP
  have hgd : ∀ (p : T) (b b' : Bool), d (gl p b) (gl p b') = |Q p b - Q p b'| := by
    intro p b b'
    have h0 : (0:ℝ) ≤ t p := (hpos p).le
    have hduv : d (tu p) (tv p) = t p := (htp p).symm
    have hdvu : d (tv p) (tu p) = t p := by rw [hd.symm]
    cases b <;> cases b' <;> simp only [hgl, hQ, if_true, if_false, Bool.false_eq_true]
    · rw [hd.diag]; simp
    · rw [hduv, zero_sub, abs_neg, abs_of_nonneg h0]
    · rw [hdvu, sub_zero, abs_of_nonneg h0]
    · rw [hd.diag]; simp
  have hP0 : ∀ y : T × ℕ, 0 ≤ P y := fun y => hposnn _ _
  have hP1 : ∀ y : T × ℕ, P y ≤ 1 := by
    intro y
    have := hposlt y.1 (y.2 + 1)
    have := ht1 y.1
    simp only [hP]
    linarith
  have hQ0 : ∀ (p : T) (b : Bool), 0 ≤ Q p b := by
    intro p b
    cases b <;> simp only [hQ, if_true, if_false, Bool.false_eq_true, le_refl]
    exact (hpos p).le
  have hQ1 : ∀ (p : T) (b : Bool), Q p b ≤ 1 := by
    intro p b
    cases b <;> simp only [hQ, if_true, if_false, Bool.false_eq_true]
    · norm_num
    · exact ht1 p
  have hp : IsPieceData d (Prod.fst : T × ℕ → T) gl
      (fun y y' => |P y - P y'|) (fun y l => |P y - Q y.1 l|) :=
    isPieceData_of_real d (Prod.fst : T × ℕ → T) gl P Q hP0 hP1 hQ0 hQ1 hgd
  set r₁ : (T × ℕ) → (T × ℕ) → ℝ := fun y y' => |P y - P y'| with hr₁
  set s₁ : (T × ℕ) → Bool → ℝ := fun y l => |P y - Q y.1 l| with hs₁
  set ω : (X ⊕ T × ℕ) → (X ⊕ T × ℕ) → ℝ :=
    glueFamily d (Prod.fst : T × ℕ → T) gl r₁ s₁ with hω
  have hωp : IsBddPseudo ω := glueFamily_isBddPseudo hd hp
  -- the chain
  set c : T → ℕ → (X ⊕ T × ℕ) := fun p j =>
    match j with
    | 0 => Sum.inl (tu p)
    | (n + 1) => Sum.inr (p, n) with hc
  have hc0 : ∀ p, c p 0 = Sum.inl (tu p) := fun p => rfl
  have hcs : ∀ p n, c p (n + 1) = Sum.inr (p, n) := fun p n => rfl
  -- distances along the chain
  have hlocus0 : ∀ (p : T) (n : ℕ), ω (Sum.inl (tu p)) (Sum.inr (p, n)) = pos p (n + 1) := by
    intro p n
    have h := glueFamily_restrict_locus (d := d) (idx := (Prod.fst : T × ℕ → T)) (g := gl)
      (r := r₁) (s := s₁) hd hp (p, n) false
    simp only [hgl, if_false, Bool.false_eq_true] at h
    rw [← hω] at h
    rw [h]
    simp only [hs₁, hQ, hP, if_false, Bool.false_eq_true]
    rw [sub_zero, abs_of_nonneg (hposnn p (n + 1))]
  have hlocus1 : ∀ (p : T) (n : ℕ),
      ω (Sum.inl (tv p)) (Sum.inr (p, n)) = t p - pos p (n + 1) := by
    intro p n
    have h := glueFamily_restrict_locus (d := d) (idx := (Prod.fst : T × ℕ → T)) (g := gl)
      (r := r₁) (s := s₁) hd hp (p, n) true
    simp only [hgl, if_true] at h
    rw [← hω] at h
    rw [h]
    simp only [hs₁, hQ, hP, if_true]
    rw [abs_of_nonpos (by linarith [hposlt p (n + 1)])]
    ring
  have hcc : ∀ (p : T) (j k : ℕ), ω (c p j) (c p k) = |pos p j - pos p k| := by
    intro p j k
    match j, k with
    | 0, 0 => rw [hωp.diag]; simp
    | 0, (m + 1) =>
        rw [hc0, hcs, hlocus0, hpos0, zero_sub, abs_neg,
          abs_of_nonneg (hposnn p (m + 1))]
    | (n + 1), 0 =>
        rw [hc0, hcs, hωp.symm (Sum.inr (p, n)) (Sum.inl (tu p)), hlocus0, hpos0, sub_zero,
          abs_of_nonneg (hposnn p (n + 1))]
    | (n + 1), (m + 1) =>
        rw [hcs, hcs]
        have h := glueFamily_restrict_piece (d := d) (idx := (Prod.fst : T × ℕ → T)) (g := gl)
          (r := r₁) (s := s₁) (y := (p, n)) (y' := (p, m)) rfl
        rw [← hω] at h
        rw [h]
  have hct : ∀ (p : T) (j : ℕ), ω (c p j) (Sum.inl (tv p)) = t p - pos p j := by
    intro p j
    match j with
    | 0 => rw [hc0, hpos0, sub_zero]; exact (htp p).symm
    | (n + 1) =>
        rw [hcs, hωp.symm (Sum.inr (p, n)) (Sum.inl (tv p)), hlocus1]
  have hgap : ∀ (p : T) (i : ℕ), ω (c p i) (c p (i + 1)) = (a p i : ℝ) := by
    intro p i
    rw [hcc p i (i + 1), hpossucc, abs_of_nonpos (by linarith [hane p i])]
    ring
  have hpre : ∀ (p : T) (j : ℕ), ω (c p 0) (c p j) = ∑ i ∈ Finset.range j, (a p i : ℝ) := by
    intro p j
    rw [hcc p 0 j, hpos0, zero_sub, abs_neg, abs_of_nonneg (hposnn p j), hposv]
  have hbase : ∀ x x', ω (Sum.inl x) (Sum.inl x') = d x x' := fun x x' => rfl
  refine ⟨ω, a, c, hωp, hbase, hc0, hapos, ?_, hgap, hpre, ?_, hasum, ?_⟩
  · intro p i
    have h1 : (a p i : ℝ) < t p := by
      have := hpossucc p i
      have := hposlt p (i + 1)
      have := hposnn p i
      linarith
    linarith [ht1 p]
  · intro p j
    rw [hct, htp, hposv]
  -- the rigidity transfer
  intro E hE hgaps hbaseE
  -- perturbations vanish along each chain
  have hchainseg : ∀ (p : T) (j m : ℕ), E (c p j) (c p (j + m)) = 0 := by
    intro p j m
    have htight : ω (c p j) (c p (j + m)) =
        ∑ i ∈ Finset.range m, ω (c p (j + i)) (c p (j + i + 1)) := by
      have hl : ω (c p j) (c p (j + m)) = pos p (j + m) - pos p j := by
        rw [hcc p j (j + m),
          abs_of_nonpos (by linarith [hposmono p j (j + m) (Nat.le_add_right j m)])]
        ring
      have hr : ∑ i ∈ Finset.range m, ω (c p (j + i)) (c p (j + i + 1)) =
          ∑ i ∈ Finset.range m, (a p (j + i) : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hgap p (j + i)
      rw [hl, hr, hseg]
    have hsum : E (c p j) (c p (j + m)) =
        ∑ i ∈ Finset.range m, E (c p (j + i)) (c p (j + i + 1)) :=
      pert_add_of_tight_chain ω E hE (fun i => c p (j + i)) htight
    have hzero : ∑ i ∈ Finset.range m, E (c p (j + i)) (c p (j + i + 1)) = 0 :=
      Finset.sum_eq_zero fun i _ => hgaps p (j + i)
    rw [hzero] at hsum
    exact hsum
  have hchain : ∀ (p : T) (j k : ℕ), E (c p j) (c p k) = 0 := by
    intro p j k
    rcases le_total j k with h | h
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hchainseg p j m
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [hE.1]
      exact hchainseg p k m
  have hchaintv : ∀ (p : T) (j : ℕ), E (c p j) (Sum.inl (tv p)) = 0 := by
    intro p j
    have htight : ω (c p 0) (Sum.inl (tv p)) =
        ω (c p 0) (c p j) + ω (c p j) (Sum.inl (tv p)) := by
      rw [hct p 0, hct p j, hpre p j, hpos0, ← hposv]
      ring
    have h := pert_add_of_tight ω E hE htight
    have h0 : E (c p 0) (Sum.inl (tv p)) = 0 := by
      rw [hc0]; exact hbaseE _ _
    have h1 : E (c p 0) (c p j) = 0 := hchain p 0 j
    linarith
  have hchaintu : ∀ (p : T) (j : ℕ), E (c p j) (Sum.inl (tu p)) = 0 := by
    intro p j
    rw [hE.1, ← hc0]
    exact hchain p 0 j
  -- cross pairs base–chain
  have hcross : ∀ (x : X) (y : T × ℕ), E (Sum.inl x) (Sum.inr y) = 0 := by
    rintro x ⟨p, n⟩
    rcases glueFamily_dichotomy_base_piece (d := d) (idx := (Prod.fst : T × ℕ → T)) (g := gl)
      (r := r₁) (s := s₁) hd hp x (p, n) with h1 | ⟨l, h1⟩
    · rw [← hω] at h1
      exact pert_eq_zero_of_dist_eq_one hE h1
    · rw [← hω] at h1
      have htight : ω (Sum.inl x) (Sum.inr (p, n)) =
          ω (Sum.inl x) (Sum.inl (gl p l)) + ω (Sum.inl (gl p l)) (Sum.inr (p, n)) := h1
      rw [pert_add_of_tight ω E hE htight, hbaseE]
      have h2 : E (Sum.inl (gl p l)) (Sum.inr (p, n)) = 0 := by
        cases l
        · simp only [hgl, if_false, Bool.false_eq_true]
          rw [hE.1, ← hcs]
          exact hchaintu p (n + 1)
        · simp only [hgl, if_true]
          rw [hE.1, ← hcs]
          exact hchaintv p (n + 1)
      rw [h2, add_zero]
  rintro (x | ⟨p, n⟩) (x' | ⟨p', n'⟩)
  · exact hbaseE x x'
  · exact hcross x (p', n')
  · rw [hE.1]; exact hcross x' (p, n)
  · by_cases hpp : p = p'
    · subst hpp
      rw [← hcs, ← hcs]
      exact hchain p (n + 1) (n' + 1)
    · rcases glueFamily_dichotomy_piece_piece (d := d) (idx := (Prod.fst : T × ℕ → T))
        (g := gl) (r := r₁) (s := s₁) hd hp (y := (p, n)) (y' := (p', n')) hpp with
        h1 | ⟨l, l', h1⟩
      · rw [← hω] at h1
        exact pert_eq_zero_of_dist_eq_one hE h1
      · rw [← hω] at h1
        set q : ℕ → (X ⊕ T × ℕ) := fun k =>
          match k with
          | 0 => Sum.inr (p, n)
          | 1 => Sum.inl (gl p l)
          | 2 => Sum.inl (gl p' l')
          | _ => Sum.inr (p', n') with hq
        have htight : ω (q 0) (q 3) = ∑ i ∈ Finset.range 3, ω (q i) (q (i + 1)) := by
          simp only [hq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          simpa using h1
        have hsum := pert_add_of_tight_chain ω E hE (m := 3) q htight
        have e0 : E (q 0) (q 1) = 0 := by
          simp only [hq]
          cases l
          · simp only [hgl, if_false, Bool.false_eq_true]
            rw [← hcs]; exact hchaintu p (n + 1)
          · simp only [hgl, if_true]
            rw [← hcs]; exact hchaintv p (n + 1)
        have e1 : E (q 1) (q 2) = 0 := by
          simp only [hq]; exact hbaseE _ _
        have e2 : E (q 2) (q 3) = 0 := by
          simp only [hq]
          cases l'
          · simp only [hgl, if_false, Bool.false_eq_true]
            rw [hE.1, ← hcs]; exact hchaintu p' (n' + 1)
          · simp only [hgl, if_true]
            rw [hE.1, ← hcs]; exact hchaintv p' (n' + 1)
        have : E (q 0) (q 3) = 0 := by
          rw [hsum]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          rw [e0, e1, e2]; ring
        simpa [hq] using this
