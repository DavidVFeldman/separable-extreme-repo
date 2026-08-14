import RequestProject.Perturbation

/-!
# Subdivision and assembly

Formalization of §4 (subdivision of a distance, paper Lemma 4.1) and the inductive skeleton
of §5 of *Every Separable Metric Space Extends to an Extreme One* (Feldman–Kehoe).

The assembly step `rigid_of_chain` is stated as a property of a *single* metric on a *fixed*
carrier, with the chain of the paper's construction given as a monotone family of subsets.
-/

set_option autoImplicit false

open Filter Topology

variable {X : Type*}

/-- Every positive real is the sum of a sequence of positive rationals. -/
theorem exists_rat_seq_hasSum {t : ℝ} (ht : 0 < t) :
    ∃ a : ℕ → ℚ, (∀ i, 0 < a i) ∧ HasSum (fun i => (a i : ℝ)) t := by
  have hex : ∀ j : ℕ, ∃ r : ℚ, t - t / 2 ^ (j+1) < (r:ℝ) ∧ (r:ℝ) < t - t / 2 ^ (j+2) := by
    intro j
    refine exists_rat_btwn ?_
    have h2 : (0:ℝ) < 2 ^ (j+1) := by positivity
    have : t / 2 ^ (j+2) < t / 2 ^ (j+1) := by
      apply div_lt_div_of_pos_left ht h2
      have : (2:ℝ) ^ (j+1) < 2 ^ (j+2) := pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  choose r hr1 hr2 using hex
  have hlt : ∀ j, (r j : ℝ) < t := by
    intro j
    have h0 : (0:ℝ) < t / 2 ^ (j+2) := by positivity
    linarith [hr2 j]
  refine ⟨fun i => Nat.casesOn i (r 0) (fun i => r (i+1) - r i), ?_, ?_⟩
  · rintro (_ | i)
    · have h2 : t / 2 ^ (0+1) < t := by rw [pow_one]; linarith
      have : (0:ℝ) < r 0 := by linarith [hr1 0]
      exact_mod_cast this
    · have h1 := hr1 (i+1)
      have h2 := hr2 i
      have hi : (i+1)+1 = i+2 := by omega
      rw [hi] at h1
      have : (0:ℝ) < (r (i+1) : ℝ) - r i := by linarith
      have : (0:ℚ) < r (i+1) - r i := by exact_mod_cast this
      simpa using this
  · set a : ℕ → ℚ := fun i => Nat.casesOn i (r 0) (fun i => r (i+1) - r i) with ha
    have hpos : ∀ i, 0 ≤ ((a i : ℚ) : ℝ) := by
      rintro (_ | i)
      · have h2 : t / 2 ^ (0+1) < t := by rw [pow_one]; linarith
        have : (0:ℝ) < r 0 := by linarith [hr1 0]
        simpa [ha] using this.le
      · have h1 := hr1 (i+1)
        have h2 := hr2 i
        have hi : (i+1)+1 = i+2 := by omega
        rw [hi] at h1
        have : (0:ℝ) ≤ (r (i+1) : ℝ) - r i := by linarith
        simpa [ha] using this
    have hpart : ∀ j : ℕ, ∑ i ∈ Finset.range (j+1), ((a i : ℚ) : ℝ) = (r j : ℝ) := by
      intro j
      induction j with
      | zero => simp [ha]
      | succ j ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [ha]
          push_cast
          ring
    have hsummable : Summable (fun i => ((a i : ℚ) : ℝ)) := by
      refine summable_of_sum_range_le (c := t) hpos ?_
      rintro (_ | n)
      · simp; linarith
      · rw [hpart n]; exact (hlt n).le
    have htend : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 t) := by
      have h1 : Tendsto (fun n : ℕ => t - t * (1/2:ℝ) ^ (n+1)) atTop (𝓝 t) := by
        have h0 : Tendsto (fun n : ℕ => t * (1/2:ℝ) ^ (n+1)) atTop (𝓝 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num)
            (by norm_num)).comp (tendsto_add_atTop_nat 1)
          simpa using this.const_mul t
        simpa using tendsto_const_nhds.sub h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds ?_ ?_
      · intro n
        have e : t * (1/2:ℝ)^(n+1) = t / 2^(n+1) := by rw [div_pow, one_pow]; ring
        simp only [e]
        linarith [hr1 n]
      · intro n; exact (hlt n).le
    rw [hsummable.hasSum_iff_tendsto_nat, ← Filter.tendsto_add_atTop_iff_nat 1]
    simpa [hpart] using htend

/-- Paper Lemma 4.1(3): along a countable geodesic from `c 0` to `y₀`, a perturbation of the
total distance is the (absolutely convergent) sum of the perturbations of the gaps. -/
theorem pert_eq_tsum_of_geodesic
    (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    (c : ℕ → X) (y₀ : X) (a : ℕ → ℝ) (t : ℝ)
    (hgap  : ∀ i, d (c i) (c (i+1)) = a i)
    (hpre  : ∀ j, d (c 0) (c j) = ∑ i ∈ Finset.range j, a i)
    (htail : ∀ j, d (c j) y₀ = t - ∑ i ∈ Finset.range j, a i)
    (hsum  : HasSum a t) :
    HasSum (fun i => ε (c i) (c (i+1))) (ε (c 0) y₀) := by
  have hdiag := h.2.1
  -- the gaps are additive along the geodesic
  have htight1 : ∀ j, ε (c 0) (c (j+1)) = ε (c 0) (c j) + ε (c j) (c (j+1)) := by
    intro j
    refine pert_add_of_tight d ε h ?_
    rw [hpre (j+1), hpre j, hgap j, Finset.sum_range_succ]
  have hpartial : ∀ j, ∑ i ∈ Finset.range j, ε (c i) (c (i+1)) = ε (c 0) (c j) := by
    intro j
    induction j with
    | zero => simpa using (hdiag (c 0)).symm
    | succ j ih => rw [Finset.sum_range_succ, ih, htight1 j]
  have htight2 : ∀ j, ε (c 0) y₀ = ε (c 0) (c j) + ε (c j) y₀ := by
    intro j
    refine pert_add_of_tight d ε h ?_
    rw [hpre j, htail j, htail 0]
    simp
  -- absolute convergence
  have hbound : ∀ i, |ε (c i) (c (i+1))| ≤ a i := by
    intro i
    have := le_trans (abs_pert_le d ε h (c i) (c (i+1))) (min_le_left _ _)
    rwa [hgap i] at this
  have hsummable : Summable (fun i => ε (c i) (c (i+1))) :=
    Summable.of_norm_bounded hsum.summable (by simpa using hbound)
  -- the tail tends to zero
  have htail0 : Tendsto (fun j => ε (c j) y₀) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun j => t - ∑ i ∈ Finset.range j, a i) (fun j => ?_) ?_
    · have := le_trans (abs_pert_le d ε h (c j) y₀) (min_le_left _ _)
      rw [htail j] at this
      simpa using this
    · have : Tendsto (fun j => t - ∑ i ∈ Finset.range j, a i) atTop (𝓝 (t - t)) :=
        tendsto_const_nhds.sub hsum.tendsto_sum_nat
      simpa using this
  rw [hsummable.hasSum_iff_tendsto_nat]
  have heq : ∀ j, ∑ i ∈ Finset.range j, ε (c i) (c (i+1)) = ε (c 0) y₀ - ε (c j) y₀ := by
    intro j
    rw [hpartial j]
    linarith [htight2 j]
  simp only [heq]
  have : Tendsto (fun j => ε (c 0) y₀ - ε (c j) y₀) atTop (𝓝 (ε (c 0) y₀ - 0)) :=
    tendsto_const_nhds.sub htail0
  simpa using this

/-- The corollary consumed by the main construction: if all the gaps along the geodesic are
frozen, the total distance is frozen. -/
theorem pert_eq_zero_of_gaps_zero
    (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    (c : ℕ → X) (y₀ : X) (a : ℕ → ℝ) (t : ℝ)
    (hgap  : ∀ i, d (c i) (c (i+1)) = a i)
    (hpre  : ∀ j, d (c 0) (c j) = ∑ i ∈ Finset.range j, a i)
    (htail : ∀ j, d (c j) y₀ = t - ∑ i ∈ Finset.range j, a i)
    (hsum  : HasSum a t)
    (hgaps : ∀ i, ε (c i) (c (i+1)) = 0) : ε (c 0) y₀ = 0 := by
  have h1 := pert_eq_tsum_of_geodesic d ε h c y₀ a t hgap hpre htail hsum
  have h2 : HasSum (fun i => ε (c i) (c (i+1))) 0 := by
    simp [hgaps]
  exact h1.unique h2

/-- Paper §5, the induction: a metric which is "locally frozen" along a chain exhausting the
space is rigid.

`S` is the chain of subsets, `N k` the points added at step `k`, `hcross` records the
dichotomy supplied by the gluing lemma. The hypothesis `hd` of the commission's statement
turned out not to be needed for the argument and is therefore not part of the statement. -/
theorem rigid_of_chain
    (d : X → X → ℝ)
    (S N : ℕ → Set X)
    (hmono  : Monotone S)
    (hcover : ∀ x : X, ∃ k, x ∈ S k)
    (hstep  : ∀ k, S (k+1) = S k ∪ N k)
    (hbase  : ∀ ε, IsPerturbation d ε → ∀ x ∈ S 0, ∀ y ∈ S 0, ε x y = 0)
    (hnew   : ∀ k, ∀ ε, IsPerturbation d ε → ∀ x ∈ N k, ∀ y ∈ N k, ε x y = 0)
    (hcross : ∀ k, ∀ x ∈ S k, ∀ y ∈ N k,
        d x y = 1 ∨ ∃ z ∈ S k ∩ N k, d x y = d x z + d z y) :
    Rigid d := by
  intro ε hpert
  have hsymm : ∀ x y, ε x y = ε y x := hpert.1
  -- the mixed case of the induction step
  have hmix : ∀ k, (∀ x ∈ S k, ∀ y ∈ S k, ε x y = 0) →
      ∀ x ∈ S k, ∀ y ∈ N k, ε x y = 0 := by
    intro k ih x hx y hy
    rcases hcross k x hx y hy with h1 | ⟨z, ⟨hzS, hzN⟩, h1⟩
    · exact pert_eq_zero_of_dist_eq_one hpert h1
    · rw [pert_add_of_tight d ε hpert h1, ih x hx z hzS, hnew k ε hpert z hzN y hy, add_zero]
  have key : ∀ k, ∀ x ∈ S k, ∀ y ∈ S k, ε x y = 0 := by
    intro k
    induction k with
    | zero => exact hbase ε hpert
    | succ k ih =>
        intro x hx y hy
        rw [hstep k] at hx hy
        rcases hx with hx | hx
        · rcases hy with hy | hy
          · exact ih x hx y hy
          · exact hmix k ih x hx y hy
        · rcases hy with hy | hy
          · rw [hsymm x y]
            exact hmix k ih y hy x hx
          · exact hnew k ε hpert x hx y hy
  intro x y
  obtain ⟨k1, hk1⟩ := hcover x
  obtain ⟨k2, hk2⟩ := hcover y
  exact key (max k1 k2) x (hmono (le_max_left k1 k2) hk1) y (hmono (le_max_right k1 k2) hk2)
