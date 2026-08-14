import RequestProject.Subdivision

/-!
# Tier 4c: the construction and Theorem 1.1

The two stages of `Subdivision.lean` and `Freeze.lean` are put together.

Every pair of points of the countable dense set `A` at distance strictly between `0` and `1`
is a *target*. Stage 1 subdivides **every** target at once into a countable chain of
rational gaps — there is no need to treat rational and irrational targets differently, since
every positive real is a sum of positive rationals. Stage 2 glues a finite rigid metric onto
every gap pair created in stage 1, which freezes all the gaps; the sum formula of
Lemma 4.1(3) then freezes every target, density (Lemma 2.5) freezes the whole of `X`, and
the two dichotomies of the family gluing lemma freeze everything else.

The input from the companion paper (Proposition 5.1: every rational in `(0,1]` is a distance
in a finite extreme metric) is carried as the explicit hypothesis `hrat`.
-/

set_option autoImplicit false

open scoped BigOperators

universe u

/-- **Paper Theorem 1.1.** Every separable bounded-by-one pseudometric space is the
restriction of a rigid (equivalently, extreme) bounded-by-one pseudometric on a space
obtained by adding countably many points.

The hypothesis `hrat` is Proposition 5.1 of the paper, quoted from the companion paper and
carried here as an explicit assumption. -/
theorem separable_extends_to_extreme {X : Type u} (d : X → X → ℝ) (hd : IsBddPseudo d)
    {A : Set X} (hA : A.Countable) (hAd : DenseFor d A)
    (hrat : ∀ q : ℚ, 0 < q → q ≤ 1 →
      ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
        IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)) :
    ∃ (Ω : Type u) (ι : X → Ω) (dt : Ω → Ω → ℝ),
      Function.Injective ι ∧ (Set.range ι)ᶜ.Countable ∧
      IsBddPseudo dt ∧ Rigid dt ∧ (∀ x y, dt (ι x) (ι y) = d x y) := by
  classical
  haveI := hA.to_subtype
  -- the targets: pairs of points of `A` at distance strictly between `0` and `1`
  set T := {p : (↥A) × (↥A) // 0 < d (p.1 : X) (p.2 : X) ∧ d (p.1 : X) (p.2 : X) < 1} with hT
  haveI : Countable T := Subtype.countable
  set tu : T → X := fun p => (p.1.1 : X) with htu
  set tv : T → X := fun p => (p.1.2 : X) with htv
  have hposT : ∀ p : T, 0 < d (tu p) (tv p) := fun p => p.2.1
  -- stage 1: subdivide every target
  obtain ⟨ω, a, c, hωp, hωbase, hc0, hapos, hale1, hgap, hpre, htail, hasum, hrigid1⟩ :=
    exists_subdivision_extension d hd tu tv hposT
  -- stage 2: freeze every gap
  set e : (T × ℕ) → Bool → (X ⊕ T × ℕ) :=
    fun j b => if b then c j.1 (j.2 + 1) else c j.1 j.2 with he
  have hfreeze : ∀ j : T × ℕ, ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
      IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = ω (e j false) (e j true) := by
    rintro ⟨p, i⟩
    have h1 : (0:ℚ) < a p i := hapos p i
    have h2 : a p i ≤ 1 := by exact_mod_cast hale1 p i
    obtain ⟨F, iF, rho, u, v, hb, hr, hv⟩ := hrat (a p i) h1 h2
    refine ⟨F, iF, rho, u, v, hb, hr, ?_⟩
    rw [hv]
    simp only [he, if_true, if_false, Bool.false_eq_true]
    exact (hgap p i).symm
  obtain ⟨dt, hdtp, hdtbase, hdtpert⟩ := exists_freezing_extension ω hωp e hfreeze
  refine ⟨(X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ, fun x => Sum.inl (Sum.inl x), dt, ?_, ?_, hdtp, ?_, ?_⟩
  · intro x y hxy
    exact Sum.inl_injective (Sum.inl_injective hxy)
  · -- only countably many points were added
    have hsub : (Set.range fun x : X => Sum.inl (Sum.inl x) :
          Set ((X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ))ᶜ ⊆
        Set.range (fun z : (T × ℕ) ⊕ ((T × ℕ) × ℕ) =>
          Sum.elim (fun y => Sum.inl (Sum.inr y)) (fun z => Sum.inr z) z) := by
      rintro ((x | y) | z) hw
      · exact absurd ⟨x, rfl⟩ hw
      · exact ⟨Sum.inl y, rfl⟩
      · exact ⟨Sum.inr z, rfl⟩
    exact Set.Countable.mono hsub (Set.countable_range _)
  · -- rigidity
    -- the key step: every perturbation vanishes on the stage-1 space
    have key : ∀ E, IsPerturbation dt E → ∀ w w', E (Sum.inl w) (Sum.inl w') = 0 := by
      intro E hE
      obtain ⟨hfrozen, -⟩ := hdtpert E hE
      set E₁ : (X ⊕ T × ℕ) → (X ⊕ T × ℕ) → ℝ := fun w w' => E (Sum.inl w) (Sum.inl w')
        with hE₁def
      have hE₁ : IsPerturbation ω E₁ := by
        have h := hE.comp (Sum.inl : (X ⊕ T × ℕ) → ((X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ))
        have heq : (fun w w' => dt (Sum.inl w) (Sum.inl w')) = ω := by
          funext w w'; exact hdtbase w w'
        rwa [heq] at h
      have hgaps : ∀ (p : T) (i : ℕ), E₁ (c p i) (c p (i + 1)) = 0 := by
        intro p i
        have := hfrozen (p, i)
        simpa [hE₁def, he] using this
      -- the perturbation restricted to `X`
      set E₀ : X → X → ℝ := fun x y => E₁ (Sum.inl x) (Sum.inl y) with hE₀def
      have hE₀ : IsPerturbation d E₀ := by
        have h := hE₁.comp (Sum.inl : X → (X ⊕ T × ℕ))
        have heq : (fun x y => ω (Sum.inl x) (Sum.inl y)) = d := by
          funext x y; exact hωbase x y
        rwa [heq] at h
      -- every target is frozen
      have hAA : ∀ x ∈ A, ∀ y ∈ A, E₀ x y = 0 := by
        intro x hx y hy
        rcases eq_or_lt_of_le (hd.nonneg x y) with h0 | h0
        · exact pert_eq_zero_of_dist_eq_zero hE₀ h0.symm
        rcases eq_or_lt_of_le (hd.le_one x y) with h1 | h1
        · exact pert_eq_zero_of_dist_eq_one hE₀ h1
        · set p : T := ⟨(⟨x, hx⟩, ⟨y, hy⟩), ⟨h0, h1⟩⟩ with hp
          have hgapω : ∀ i, ω (c p i) (c p (i + 1)) = ((a p i : ℝ)) := hgap p
          have hthis := pert_eq_zero_of_gaps_zero ω E₁ hE₁ (c p) (Sum.inl (tv p))
            (fun i => (a p i : ℝ)) (d (tu p) (tv p)) hgapω (hpre p) (htail p) (hasum p)
            (hgaps p)
          rw [hc0 p] at hthis
          exact hthis
      have hX : ∀ x y, E₀ x y = 0 := pert_eq_zero_of_dense d E₀ hE₀ hAd hAA
      exact hrigid1 E₁ hE₁ hgaps (fun x x' => hX x x')
    -- assemble via the induction of paper §5
    set S : ℕ → Set ((X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ) := fun k =>
      match k with
      | 0 => Set.range fun x : X => Sum.inl (Sum.inl x)
      | 1 => Set.range (Sum.inl : (X ⊕ T × ℕ) → _)
      | _ => Set.univ with hS
    set N : ℕ → Set ((X ⊕ T × ℕ) ⊕ (T × ℕ) × ℕ) := fun k =>
      match k with
      | 0 => Set.range (Sum.inl : (X ⊕ T × ℕ) → _)
      | _ => Set.univ with hN
    have hmono : Monotone S := by
      refine monotone_nat_of_le_succ fun k => ?_
      match k with
      | 0 =>
          rintro w ⟨x, rfl⟩
          exact ⟨Sum.inl x, rfl⟩
      | 1 => exact fun w _ => Set.mem_univ w
      | (n + 2) => exact fun w _ => Set.mem_univ w
    have hcover : ∀ w, ∃ k, w ∈ S k := fun w => ⟨2, Set.mem_univ w⟩
    have hstep : ∀ k, S (k + 1) = S k ∪ N k := by
      intro k
      match k with
      | 0 =>
          apply Set.Subset.antisymm
          · exact fun w hw => Or.inr hw
          · rintro w (⟨x, rfl⟩ | hw)
            · exact ⟨Sum.inl x, rfl⟩
            · exact hw
      | 1 => exact (Set.union_univ _).symm
      | (n + 2) => exact (Set.union_univ _).symm
    refine rigid_of_chain dt S N hmono hcover hstep ?_ ?_ ?_
    · rintro E hE w ⟨x, rfl⟩ w' ⟨y, rfl⟩
      exact key E hE (Sum.inl x) (Sum.inl y)
    · intro k E hE
      match k with
      | 0 =>
          rintro w ⟨u, rfl⟩ w' ⟨u', rfl⟩
          exact key E hE u u'
      | (n + 1) =>
          intro w _ w' _
          obtain ⟨-, hall⟩ := hdtpert E hE
          exact hall (fun u u' => key E hE u u') w w'
    · intro k w hw w' _
      refine Or.inr ⟨w, ⟨hw, ?_⟩, ?_⟩
      · match k with
        | 0 =>
            obtain ⟨x, rfl⟩ := hw
            exact ⟨Sum.inl x, rfl⟩
        | (n + 1) => exact Set.mem_univ w
      · rw [hdtp.diag, zero_add]
  · intro x y
    rw [hdtbase (Sum.inl x) (Sum.inl y)]
    exact hωbase x y

/-- **Paper Theorem 1.1, extreme-point form.** The extension is an extreme point of the
convex set of bounded-by-one pseudometrics on the extended space, and the extended space is
again separable. -/
theorem separable_extends_to_extremePoint {X : Type u} (d : X → X → ℝ) (hd : IsBddPseudo d)
    {A : Set X} (hA : A.Countable) (hAd : DenseFor d A)
    (hrat : ∀ q : ℚ, 0 < q → q ≤ 1 →
      ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
        IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ)) :
    ∃ (Ω : Type u) (ι : X → Ω) (dt : Ω → Ω → ℝ) (B : Set Ω),
      Function.Injective ι ∧ (Set.range ι)ᶜ.Countable ∧
      dt ∈ (bddPseudoSet Ω).extremePoints ℝ ∧ (∀ x y, dt (ι x) (ι y) = d x y) ∧
      B.Countable ∧ DenseFor dt B := by
  obtain ⟨Ω, ι, dt, hinj, hcount, hdtp, hrig, hres⟩ :=
    separable_extends_to_extreme d hd hA hAd hrat
  refine ⟨Ω, ι, dt, (ι '' A) ∪ (Set.range ι)ᶜ, hinj, hcount,
    (rigid_iff_extremePoint dt hdtp).mp hrig, hres, ?_, ?_⟩
  · exact ((hA.image ι).union hcount)
  · intro w η hη
    by_cases hw : w ∈ Set.range ι
    · obtain ⟨x, rfl⟩ := hw
      obtain ⟨b, hbA, hxb⟩ := hAd x η hη
      exact ⟨ι b, Or.inl ⟨b, hbA, rfl⟩, by rw [hres]; exact hxb⟩
    · exact ⟨w, Or.inr hw, by rw [hdtp.diag]; exact hη⟩
