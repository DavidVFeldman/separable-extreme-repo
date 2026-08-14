import RequestProject.GlueFamily
import RequestProject.Bowtie

/-!
# Lower bounds: isolation in an amalgam, and in a bowtie

Tier 6c needs the *opposite* of the estimates of Tiers 4 and 5: not that glued points are
close enough to satisfy the triangle inequality, but that they are far enough apart to be
isolated. Two ingredients:

* `glueFamily_piece_isolated`: a new point of a piece is at distance `0` or `≥ c` from every
  point of the amalgam, as soon as `c` bounds its distances to the locus of its own piece
  from below and its nonzero distances inside its own piece;
* `glueFamily_base_isolated`: the same for a point of the base, with the two hypotheses one
  has to check there;
* `Bowtie.inv_le_bowtie`: distinct points of the bowtie `B_b` are at distance at least `1/b`.

Both amalgam lemmas are proved from the definition of `glueFamily` by the same two
observations: the base-to-piece distance is an infimum of `d + s` and `d ≥ 0`, and the
piece-to-piece distance is an infimum of `s + (base-to-piece)` with both terms nonnegative.
-/

set_option autoImplicit false

variable {X Y I L : Type*}

section

variable [Fintype L] [Nonempty L] {d : X → X → ℝ} {idx : Y → I} {g : I → L → X}
  {r : Y → Y → ℝ} {s : Y → L → ℝ}

theorem le_gfBasePiece (hd : IsBddPseudo d) {c : ℝ} (x : X) (y : Y)
    (hs : ∀ l, c ≤ s y l) : c ≤ gfBasePiece d idx g s x y := by
  refine Finset.le_inf' _ _ fun l _ => ?_
  have := hd.nonneg x (g (idx y) l)
  have := hs l
  linarith

theorem le_gfPiecePiece (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s) {c : ℝ}
    (y y' : Y) (hs : ∀ l, c ≤ s y l) : c ≤ gfPiecePiece d idx g s y y' := by
  refine Finset.le_inf' _ _ fun l _ => ?_
  have h1 := hs l
  have h2 := gfBasePiece_nonneg hd hp (g (idx y) l) y'
  linarith

variable [DecidableEq I]

/-- **A new point of a piece is isolated in the amalgam**: every other point is at distance
at least `c`, provided `c` bounds its distances to its own locus from below and its
distances to the other points of its own piece. -/
theorem glueFamily_piece_isolated (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s)
    {c : ℝ} (hc1 : c ≤ 1) (y : Y) (hs : ∀ l, c ≤ s y l)
    (hr : ∀ y', idx y' = idx y → y' = y ∨ c ≤ r y y') {z : X ⊕ Y} (hz : z ≠ Sum.inr y) :
    c ≤ glueFamily d idx g r s (Sum.inr y) z := by
  rcases z with x | y'
  · rw [glueFamily_inr_inl]
    exact le_min hc1 (le_gfBasePiece hd x y hs)
  · rw [glueFamily_inr_inr]
    by_cases h : idx y = idx y'
    · rw [if_pos h]
      rcases hr y' h.symm with rfl | hc
      · exact absurd rfl hz
      · exact hc
    · rw [if_neg h]
      exact le_min hc1 (le_gfPiecePiece hd hp y y' hs)

/-- **A point of the base is isolated in the amalgam**, given the two estimates one has to
check: distances inside the base, and the two-leg paths to the new points. -/
theorem glueFamily_base_isolated {c : ℝ} (hc1 : c ≤ 1) (x : X)
    (hbase : ∀ x', x' = x ∨ c ≤ d x x')
    (hpiece : ∀ (y : Y) (l : L), c ≤ d x (g (idx y) l) + s y l) {z : X ⊕ Y}
    (hz : z ≠ Sum.inl x) : c ≤ glueFamily d idx g r s (Sum.inl x) z := by
  rcases z with x' | y
  · rcases hbase x' with rfl | hc
    · exact absurd rfl hz
    · exact hc
  · rw [glueFamily_inl_inr]
    exact le_min hc1 (Finset.le_inf' _ _ fun l _ => hpiece y l)

end

namespace Bowtie

/-- Distinct points of the bowtie are at raw distance at least `1`. -/
theorem one_le_raw_of_ne {b : ℕ} {x y : Bw b} (h : x ≠ y) : (1 : ℝ) ≤ raw b x y := by
  by_cases hl : lvl x = lvl y
  · rw [raw_of_lvl_eq hl h]; norm_num
  · rw [raw_of_lvl_ne hl]
    exact one_le_abs_lvl_sub hl

/-- **Distinct points of the bowtie `B_b` are at distance at least `1/b`.** -/
theorem inv_le_bowtie {b : ℕ} (hb : 2 ≤ b) {x y : Bw b} (h : x ≠ y) :
    ((b : ℝ))⁻¹ ≤ bowtie b x y := by
  have hbpos : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [bowtie, le_div_iff₀ hbpos, inv_mul_cancel₀ (ne_of_gt hbpos)]
  exact one_le_raw_of_ne h

/-- Either two points of the bowtie are at distance `0`, or at distance at least `1/b`. -/
theorem bowtie_zero_or_inv_le {b : ℕ} (hb : 2 ≤ b) (x y : Bw b) :
    bowtie b x y = 0 ∨ ((b : ℝ))⁻¹ ≤ bowtie b x y := by
  by_cases h : x = y
  · subst h; left; simp [bowtie]
  · exact Or.inr (inv_le_bowtie hb h)

end Bowtie
