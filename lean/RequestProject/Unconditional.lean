import RequestProject.Construct
import RequestProject.Corollary
import RequestProject.Bowtie

/-!
# Tier 5: the unconditional forms of Theorem 1.1 and Corollary 1.2

`RequestProject/Bowtie.lean` proves Proposition 5.1 (`exists_finite_rigid_realizing`), which
the earlier tiers carried as the hypothesis `hrat`.  Discharging it gives the primed forms
below.  The hypothesised forms are kept as well: they document the dependency structure.
-/

set_option autoImplicit false

universe u

/-- **Paper Theorem 1.1, unconditional.** Every separable bounded-by-one pseudometric space
is the restriction of a rigid bounded-by-one pseudometric on a space obtained by adding
countably many points.

This is `separable_extends_to_extreme` with the hypothesis `hrat` (Proposition 5.1)
discharged by `exists_finite_rigid_realizing`. -/
theorem separable_extends_to_extreme' {X : Type u} (d : X → X → ℝ) (hd : IsBddPseudo d)
    {A : Set X} (hA : A.Countable) (hAd : DenseFor d A) :
    ∃ (Ω : Type u) (ι : X → Ω) (dt : Ω → Ω → ℝ),
      Function.Injective ι ∧ (Set.range ι)ᶜ.Countable ∧
      IsBddPseudo dt ∧ Rigid dt ∧ (∀ x y, dt (ι x) (ι y) = d x y) :=
  separable_extends_to_extreme d hd hA hAd exists_finite_rigid_realizing

/-- **Paper Theorem 1.1, extreme-point form, unconditional.** -/
theorem separable_extends_to_extremePoint' {X : Type u} (d : X → X → ℝ) (hd : IsBddPseudo d)
    {A : Set X} (hA : A.Countable) (hAd : DenseFor d A) :
    ∃ (Ω : Type u) (ι : X → Ω) (dt : Ω → Ω → ℝ) (B : Set Ω),
      Function.Injective ι ∧ (Set.range ι)ᶜ.Countable ∧
      dt ∈ (bddPseudoSet Ω).extremePoints ℝ ∧ (∀ x y, dt (ι x) (ι y) = d x y) ∧
      B.Countable ∧ DenseFor dt B :=
  separable_extends_to_extremePoint d hd hA hAd exists_finite_rigid_realizing

/-- **Paper Corollary 1.2, unconditional.** For any countable `V ⊆ [0,1]` there is a
countable space carrying an extreme (rigid) bounded-by-one pseudometric all of whose
prescribed values `v ∈ V` occur as distances. -/
theorem exists_countable_extreme_realizing' (V : Set ℝ) (hV : V.Countable)
    (hV0 : ∀ v ∈ V, 0 ≤ v) (hV1 : ∀ v ∈ V, v ≤ 1) :
    ∃ (Ω : Type) (dt : Ω → Ω → ℝ),
      Countable Ω ∧ IsBddPseudo dt ∧ Rigid dt ∧
      dt ∈ (bddPseudoSet Ω).extremePoints ℝ ∧
      ∀ v ∈ V, ∃ x y : Ω, dt x y = v :=
  exists_countable_extreme_realizing V hV hV0 hV1 exists_finite_rigid_realizing
