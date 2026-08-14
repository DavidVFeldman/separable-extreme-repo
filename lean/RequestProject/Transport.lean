import RequestProject.Chain

/-!
# Transport of metrics, perturbations and rigidity along maps

Small toolbox used by the Tier 4 construction: pulling a bounded-by-one pseudometric and a
perturbation back along an arbitrary map, transporting rigidity along a *surjection*, and
the consequence that a perturbation vanishes on any isometric copy of a rigid metric.
-/

set_option autoImplicit false

variable {X Z : Type*}

/-- The pullback of a bounded-by-one pseudometric along any map is one. -/
theorem IsBddPseudo.comp {d : X → X → ℝ} (hd : IsBddPseudo d) (φ : Z → X) :
    IsBddPseudo (fun a b => d (φ a) (φ b)) :=
  ⟨fun _ _ => hd.nonneg _ _, fun _ _ => hd.le_one _ _, fun _ => hd.diag _,
    fun _ _ => hd.symm _ _, fun _ _ _ => hd.triangle _ _ _⟩

/-- The pullback of a perturbation along any map is a perturbation of the pullback. -/
theorem IsPerturbation.comp {d ε : X → X → ℝ} (h : IsPerturbation d ε) (φ : Z → X) :
    IsPerturbation (fun a b => d (φ a) (φ b)) (fun a b => ε (φ a) (φ b)) := by
  obtain ⟨hsymm, hdiag, hplus, hminus⟩ := h
  exact ⟨fun _ _ => hsymm _ _, fun _ => hdiag _, hplus.comp φ, hminus.comp φ⟩

/-- **Rigidity transports along surjections.** If `ρ` is rigid then so is its pullback
along a surjection: a perturbation of the pullback descends, because points with the same
image are at distance `0` and hence indistinguishable by a perturbation. -/
theorem Rigid.comp_surjective {F G : Type*} {ρ : F → F → ℝ} (hrig : Rigid ρ)
    {θ : G → F} (hθ : Function.Surjective θ) : Rigid (fun a b => ρ (θ a) (θ b)) := by
  intro e hpert
  choose sec hsec using hθ
  set σ : G → G → ℝ := fun a b => ρ (θ a) (θ b) with hσ
  have hσp : IsBddPseudo σ := hpert.isBddPseudo
  -- the perturbation descends to `ρ` along the chosen section
  have hdesc : ∀ a b : F, e (sec a) (sec b) = 0 := by
    have hp : IsPerturbation ρ (fun a b => e (sec a) (sec b)) := by
      have h := hpert.comp sec
      have heq : (fun a b => σ (sec a) (sec b)) = ρ := by
        funext a b; simp [hσ, hsec]
      rwa [heq] at h
    exact fun a b => hrig _ hp a b
  -- a point may be replaced by the chosen representative of its image
  have hmove : ∀ g g' : G, e g g' = e (sec (θ g)) g' := by
    intro g g'
    have h0 : σ g (sec (θ g)) = 0 := by
      have : θ (sec (θ g)) = θ g := hsec (θ g)
      simp only [hσ, this]
      exact hσp.diag g
    have htight : σ g g' = σ g (sec (θ g)) + σ (sec (θ g)) g' := by
      have hth : θ (sec (θ g)) = θ g := hsec (θ g)
      have h2 : σ (sec (θ g)) g' = σ g g' := by simp only [hσ, hth]
      rw [h0, h2, zero_add]
    have h1 := pert_add_of_tight σ e hpert htight
    have hz : e g (sec (θ g)) = 0 := pert_eq_zero_of_dist_eq_zero hpert h0
    linarith
  intro g g'
  have h1 : e g g' = e (sec (θ g)) g' := hmove g g'
  have h2 : e (sec (θ g)) g' = e g' (sec (θ g)) := hpert.1 _ _
  have h3 : e g' (sec (θ g)) = e (sec (θ g')) (sec (θ g)) := hmove g' _
  rw [h1, h2, h3, hdesc]

/-- A perturbation vanishes on any isometric copy of a rigid metric. -/
theorem pert_eq_zero_of_isometry {Ω F : Type*} {D E : Ω → Ω → ℝ} (h : IsPerturbation D E)
    {ρ : F → F → ℝ} (hrig : Rigid ρ) (φ : F → Ω) (hiso : ∀ a b, D (φ a) (φ b) = ρ a b) :
    ∀ a b, E (φ a) (φ b) = 0 := by
  have hp : IsPerturbation ρ (fun a b => E (φ a) (φ b)) := by
    have h' := h.comp φ
    have heq : (fun a b => D (φ a) (φ b)) = ρ := by
      funext a b; exact hiso a b
    rwa [heq] at h'
  exact fun a b => hrig _ hp a b
