import RequestProject.Stage1
import RequestProject.Stage2

/-!
# Tier 6b: the canonical extension `E(A)`

Definition 6.2 of the paper, on an explicit carrier and with no choices left open.

*Stage 1.* For every **ordered** pair `(u,v)` of points of `A` at irrational distance, the
canonical subdivision chain of `Bits.lean` is glued in: the new points sit at the partial
sums of the canonical gaps of `d u v`. The index set is the type `Chains A d` of such
ordered pairs, so no enumeration and no choice of subdivision is involved.

*Stage 2.* For every **ordered** pair to be frozen — a pair of points of `A` at a positive
rational distance, or an adjacent gap pair of a stage-1 chain, in either orientation — the
canonical bowtie of `Stage2.lean` is glued in.

The results of this file are the shape of the commission: `E_isBddPseudo`, `E_extends` and
`E_rigid`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Canonical

universe u

variable {A : Type u} (d : A → A → ℝ)

/-! ### Stage 1 -/

/-- The stage-1 index set: ordered pairs of `A` at irrational distance. -/
def Chains (A : Type u) (d : A → A → ℝ) : Type u := {p : A × A // Irrational (d p.1 p.2)}

/-- The first point of a chain pair. -/
def cu (p : Chains A d) : A := p.val.1

/-- The second point of a chain pair. -/
def cv (p : Chains A d) : A := p.val.2

theorem cirr (p : Chains A d) : Irrational (d (cu d p) (cv d p)) := p.property

/-- The canonical gaps of the chain over `p`. -/
noncomputable def cgaps (p : Chains A d) (i : ℕ) : ℝ := (cgap (d (cu d p) (cv d p)) i : ℝ)

/-- The stage-1 carrier: `A` together with the points of all the canonical chains. -/
abbrev W1 (A : Type u) (d : A → A → ℝ) : Type u := A ⊕ (Chains A d × ℕ)

/-- The stage-1 distance. -/
noncomputable def dist1 : W1 A d → W1 A d → ℝ :=
  Stage1.subDist d (cu d) (cv d) (cgaps d)

/-- The `j`-th point of the canonical chain over `p`. -/
noncomputable def chp (p : Chains A d) (j : ℕ) : W1 A d := Stage1.chainPt (cu d) p j

theorem irr_pos {t : ℝ} (h : Irrational t) (h0 : 0 ≤ t) : 0 < t := by
  rcases h0.lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ h) (by simp)

theorem irr_lt_one {t : ℝ} (h : Irrational t) (h1 : t ≤ 1) : t < 1 := by
  rcases h1.lt_or_eq with h2 | h2
  · exact h2
  · exact absurd (h2 ▸ h) (by simp)

theorem cgaps_pos (p : Chains A d) (i : ℕ) : 0 < cgaps d p i := by
  have := cgap_pos (d (cu d p) (cv d p)) i
  simpa [cgaps] using this

@[simp] theorem dist1_base (a a' : A) : dist1 d (Sum.inl a) (Sum.inl a') = d a a' := rfl

section

variable {d} (hd : IsBddPseudo d)

include hd

theorem cdist_pos (p : Chains A d) : 0 < d (cu d p) (cv d p) :=
  irr_pos (cirr d p) (hd.nonneg _ _)

theorem cdist_lt_one (p : Chains A d) : d (cu d p) (cv d p) < 1 :=
  irr_lt_one (cirr d p) (hd.le_one _ _)

theorem cgaps_hasSum (p : Chains A d) :
    HasSum (fun i => cgaps d p i) (d (cu d p) (cv d p)) :=
  hasSum_cgap (cdist_pos hd p) (cdist_lt_one hd p) (cirr d p)

theorem dist1_isBddPseudo : IsBddPseudo (dist1 d) :=
  Stage1.subDist_isBddPseudo hd (cgaps_pos d) (cgaps_hasSum hd)

theorem dist1_gap (p : Chains A d) (i : ℕ) :
    dist1 d (chp d p i) (chp d p (i + 1)) = cgaps d p i :=
  Stage1.subDist_gap hd (cgaps_pos d) (cgaps_hasSum hd) p i

end

/-! ### Stage 2 -/

/-- The stage-2 index set for the core pairs: ordered pairs of `A` at a positive rational
distance. -/
def RatPairs (A : Type u) (d : A → A → ℝ) : Type u :=
  {p : A × A // ¬ Irrational (d p.1 p.2) ∧ 0 < d p.1 p.2}

/-- The stage-2 index set: the core pairs at rational distance, and the adjacent gap pairs
of the stage-1 chains, in both orientations. -/
def Bows (A : Type u) (d : A → A → ℝ) : Type u :=
  RatPairs A d ⊕ (Chains A d × ℕ × Bool)

/-- The two anchors of a stage-2 piece. -/
noncomputable def banc : Bows A d → Bool → W1 A d
  | Sum.inl p, false => Sum.inl p.val.1
  | Sum.inl p, true => Sum.inl p.val.2
  | Sum.inr (p, n, o), l => chp d p (if l = o then n else n + 1)

/-- **The canonical extension**: the carrier of `E(A)`. -/
def ECarrier (A : Type u) (d : A → A → ℝ) : Type u :=
  W1 A d ⊕ Stage2.Decor2 (dist1 d) (banc d)

/-- **The canonical extension**: the distance of `E(A)`. -/
noncomputable def EDist : ECarrier A d → ECarrier A d → ℝ :=
  Stage2.frzDist (dist1 d) (banc d)

/-- The copy of `A` inside `E(A)`. -/
def einl (a : A) : ECarrier A d := Sum.inl (Sum.inl a)

/-- The copy of the stage-1 space inside `E(A)`. -/
def ew1 (w : W1 A d) : ECarrier A d := Sum.inl w

section

variable {d} (hd : IsBddPseudo d)

include hd

theorem banc_pos (j : Bows A d) : 0 < dist1 d (banc d j false) (banc d j true) := by
  match j with
  | Sum.inl p =>
      have h : dist1 d (banc d (Sum.inl p) false) (banc d (Sum.inl p) true)
          = d p.val.1 p.val.2 := rfl
      rw [h]
      exact p.property.2
  | Sum.inr (p, n, o) =>
      have hgap := dist1_gap hd p n
      have hsymm := (dist1_isBddPseudo hd).symm
      have hpos := cgaps_pos d p n
      cases o
      · show 0 < dist1 d (chp d p n) (chp d p (n + 1))
        rw [hgap]; exact hpos
      · show 0 < dist1 d (chp d p (n + 1)) (chp d p n)
        rw [hsymm, hgap]; exact hpos

theorem banc_rat (j : Bows A d) :
    ¬ Irrational (dist1 d (banc d j false) (banc d j true)) := by
  match j with
  | Sum.inl p =>
      have h : dist1 d (banc d (Sum.inl p) false) (banc d (Sum.inl p) true)
          = d p.val.1 p.val.2 := rfl
      rw [h]
      exact p.property.1
  | Sum.inr (p, n, o) =>
      have hgap := dist1_gap hd p n
      have hsymm := (dist1_isBddPseudo hd).symm
      have hcast : cgaps d p n = ((cgap (d (cu d p) (cv d p)) n : ℚ) : ℝ) := rfl
      cases o
      · show ¬ Irrational (dist1 d (chp d p n) (chp d p (n + 1)))
        rw [hgap, hcast]
        exact Rat.not_irrational _
      · show ¬ Irrational (dist1 d (chp d p (n + 1)) (chp d p n))
        rw [hsymm, hgap, hcast]
        exact Rat.not_irrational _

/-- **`E(A)` is a bounded-by-one pseudometric space.** -/
theorem E_isBddPseudo : IsBddPseudo (EDist d) :=
  Stage2.frzDist_isBddPseudo (dist1_isBddPseudo hd) (banc_pos hd) (banc_rat hd)

omit hd in
/-- **`E(A)` extends `A`.** -/
@[simp] theorem E_extends (a a' : A) : EDist d (einl d a) (einl d a') = d a a' := rfl

omit hd in
@[simp] theorem E_w1 (w w' : W1 A d) : EDist d (ew1 d w) (ew1 d w') = dist1 d w w' := rfl

/-! ### Rigidity -/

/-- **`E(A)` is rigid**, hence an extreme point of the convex set of bounded-by-one
pseudometrics on its carrier. -/
theorem E_rigid : Rigid (EDist d) := by
  intro E hE
  have hd1 : IsBddPseudo (dist1 d) := dist1_isBddPseudo hd
  have hq0 := banc_pos hd
  have hrat := banc_rat hd
  -- the restriction of the perturbation to the stage-1 space
  set E₁ : W1 A d → W1 A d → ℝ := fun w w' => E (Sum.inl w) (Sum.inl w') with hE₁def
  have hE₁ : IsPerturbation (dist1 d) E₁ := by
    have h := hE.comp (Sum.inl : W1 A d → ECarrier A d)
    have heq : (fun w w' => EDist d (Sum.inl w) (Sum.inl w')) = dist1 d := rfl
    rwa [heq] at h
  -- stage 2 freezes every target pair
  have hfrozen : ∀ j : Bows A d, E₁ (banc d j false) (banc d j true) = 0 :=
    fun j => Stage2.frz_pert_target hd1 hq0 hrat E hE j
  -- in particular every gap of every chain
  have hgaps : ∀ (p : Chains A d) (i : ℕ), E₁ (chp d p i) (chp d p (i + 1)) = 0 := by
    intro p i
    exact hfrozen (Sum.inr (p, i, false))
  -- and every pair of `A`
  have hA : ∀ a a' : A, E₁ (Sum.inl a) (Sum.inl a') = 0 := by
    intro a a'
    by_cases hirr : Irrational (d a a')
    · -- subdivided: the gaps add up to the whole distance
      set p : Chains A d := ⟨(a, a'), hirr⟩ with hp
      have hcu : cu d p = a := rfl
      have hcv : cv d p = a' := rfl
      have h := pert_eq_zero_of_gaps_zero (dist1 d) E₁ hE₁ (chp d p) (Sum.inl (cv d p))
        (cgaps d p) (d (cu d p) (cv d p))
        (dist1_gap hd p)
        (fun j => by
          have := Stage1.subDist_pre hd (cgaps_pos d) (cgaps_hasSum hd) p j
          simpa [chp, dist1, Stage1.spos] using this)
        (fun j => by
          have := Stage1.subDist_tail hd (cgaps_pos d) (cgaps_hasSum hd) p j
          simpa [chp, dist1, Stage1.spos] using this)
        (cgaps_hasSum hd p) (hgaps p)
      simpa [chp, Stage1.chainPt, hcu, hcv] using h
    · rcases eq_or_lt_of_le (hd.nonneg a a') with h0 | h0
      · exact pert_eq_zero_of_dist_eq_zero hE₁ h0.symm
      · exact hfrozen (Sum.inl ⟨(a, a'), hirr, h0⟩)
  -- stage 1 then freezes the whole stage-1 space
  have hW1 : ∀ w w', E₁ w w' = 0 :=
    Stage1.subDist_rigid_transfer hd (cgaps_pos d) (cgaps_hasSum hd) E₁ hE₁ hgaps hA
  -- and stage 2 freezes everything else
  exact Stage2.frz_pert_transfer hd1 hq0 hrat E hE hW1

/-- **`E(A)` is an extreme point** of the convex set of bounded-by-one pseudometrics. -/
theorem E_extremePoint : EDist d ∈ (bddPseudoSet (ECarrier A d)).extremePoints ℝ :=
  (rigid_iff_extremePoint (EDist d) (E_isBddPseudo hd)).mp (E_rigid hd)

end

end Canonical
