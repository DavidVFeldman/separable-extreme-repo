import RequestProject.LowerBounds
import RequestProject.Stage1
import RequestProject.Stage2

/-!
# Isolation of the new points of the two stages

The new points of both stages of the canonical extension are *isolated*, with an explicit
radius:

* a new point of a stage-1 chain is at distance at least `cdel` from every other point of
  the stage-1 amalgam, where `cdel` is the minimum of its distances to the two anchors of
  its chain and of the two gaps adjacent to it;
* a new point of a stage-2 bowtie is at distance at least `1/b` from every other point of
  the stage-2 amalgam, where `b` is the size of its bowtie.

Both are instances of `glueFamily_piece_isolated`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Stage1

variable {X T : Type*}

/-- The isolation radius of the `n`-th new point of the chain over `p`: the smaller of its
distances to the two anchors, and of the two gaps adjacent to it. -/
noncomputable def cdel (d : X → X → ℝ) (tu tv : T → X) (a : T → ℕ → ℝ) (p : T) (n : ℕ) : ℝ :=
  min (min (spos a p (n + 1)) (d (tu p) (tv p) - spos a p (n + 1))) (min (a p n) (a p (n + 1)))

section

variable {d : X → X → ℝ} {tu tv : T → X} {a : T → ℕ → ℝ}
  (hd : IsBddPseudo d) (hapos : ∀ p i, 0 < a p i)
  (hasum : ∀ p, HasSum (fun i => a p i) (d (tu p) (tv p)))

include hapos

theorem spos_pos (p : T) (n : ℕ) : 0 < spos a p (n + 1) := by
  refine Finset.sum_pos (fun i _ => hapos p i) ⟨0, ?_⟩
  simp

include hasum

theorem cdel_pos (p : T) (n : ℕ) : 0 < cdel d tu tv a p n := by
  have h1 := spos_pos hapos p n
  have h2 := spos_lt hapos hasum p (n + 1)
  have h3 := hapos p n
  have h4 := hapos p (n + 1)
  simp only [cdel, lt_min_iff]
  refine ⟨⟨h1, by linarith⟩, h3, h4⟩

include hd

theorem cdel_le_one (p : T) (n : ℕ) : cdel d tu tv a p n ≤ 1 := by
  have h1 := spos_lt hapos hasum p (n + 1)
  have h2 := hd.le_one (tu p) (tv p)
  have : spos a p (n + 1) ≤ 1 := by linarith
  exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) this)

/-- **The new points of a stage-1 chain are isolated.** -/
theorem subDist_chain_isolated (p : T) (n : ℕ) {z : X ⊕ T × ℕ} (hz : z ≠ Sum.inr (p, n)) :
    cdel d tu tv a p n ≤ subDist d tu tv a (Sum.inr (p, n)) z := by
  classical
  have hnn : ∀ (q : T) (j : ℕ), 0 ≤ spos a q j := spos_nonneg hapos
  have hs : ∀ l : Bool, cdel d tu tv a p n ≤ |ppos a (p, n) - qval d tu tv (p, n).1 l| := by
    intro l
    cases l
    · have : |ppos a (p, n) - qval d tu tv p false| = spos a p (n + 1) := by
        simp only [ppos, qval, if_false, Bool.false_eq_true, sub_zero]
        exact abs_of_nonneg (hnn p (n + 1))
      rw [this]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    · have hlt := spos_lt hapos hasum p (n + 1)
      have : |ppos a (p, n) - qval d tu tv p true| = d (tu p) (tv p) - spos a p (n + 1) := by
        simp only [ppos, qval, if_true]
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [this]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hr : ∀ y' : T × ℕ, y'.1 = (p, n).1 →
      y' = (p, n) ∨ cdel d tu tv a p n ≤ |ppos a (p, n) - ppos a y'| := by
    rintro ⟨q, m⟩ hq
    simp only at hq
    subst hq
    rcases eq_or_ne m n with rfl | hmn
    · exact Or.inl rfl
    · right
      simp only [ppos]
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have h1 : spos a q (m + 1) ≤ spos a q n := spos_mono hapos q (by omega)
        have h2 : spos a q (n + 1) = spos a q n + a q n := spos_succ a q n
        have h3 : 0 < a q n := hapos q n
        rw [abs_of_nonneg (by linarith)]
        exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
      · have h1 : spos a q (n + 2) ≤ spos a q (m + 1) := spos_mono hapos q (by omega)
        have h2 : spos a q (n + 2) = spos a q (n + 1) + a q (n + 1) := spos_succ a q (n + 1)
        have h3 : 0 < a q (n + 1) := hapos q (n + 1)
        rw [abs_of_nonpos (by linarith)]
        refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))
  exact glueFamily_piece_isolated hd (piece_data hd hapos hasum)
    (cdel_le_one hd hapos hasum p n) (p, n) hs hr hz

end

end Stage1

namespace Stage2

open Canonical

variable {W J : Type*}

section

variable {D : W → W → ℝ} {banc : J → Bool → W} (hD : IsBddPseudo D)
  (hq0 : ∀ j, 0 < D (banc j false) (banc j true))
  (hrat : ∀ j, ¬ Irrational (D (banc j false) (banc j true)))

include hD hq0 hrat

omit hD hq0 hrat in
theorem toBw_dPos (z : Decor2 D banc) :
    toBw (bsz D banc (dIdx z)) (dPos z)
      = Bowtie.pt (⟨z.val.2.1, z.property.1⟩ : Fin (bsz D banc (dIdx z))) z.val.2.2 :=
  toBw_pt (⟨z.val.2.1, z.property.1⟩ : Fin (bsz D banc (dIdx z))) z.val.2.2

omit hD hq0 hrat in
theorem inv_bsz_le_one (j : J) : (((bsz D banc j : ℕ) : ℝ))⁻¹ ≤ 1 := by
  have h : (2 : ℝ) ≤ ((bsz D banc j : ℕ) : ℝ) := by
    exact_mod_cast two_le_bsz (D := D) (banc := banc) j
  rw [inv_le_one₀ (by linarith)]
  linarith

/-- **A new point of a stage-2 bowtie is at distance at least `1/b` from the two anchors of
its bowtie.** -/
theorem inv_bsz_le_pieceAnc (z : Decor2 D banc) (l : Bool) :
    (((bsz D banc (dIdx z) : ℕ) : ℝ))⁻¹ ≤
      pieceDist D banc (dIdx z) (dPos z) (pieceAnc D banc (dIdx z) l) := by
  have hb2 : 2 ≤ bsz D banc (dIdx z) := two_le_bsz (D := D) (banc := banc) (dIdx z)
  have hzpt := toBw_dPos z
  simp only [pieceDist]
  refine Bowtie.inv_le_bowtie hb2 ?_
  cases l
  · rw [hzpt, pieceAnc, if_neg (by simp)]
    simp [Bowtie.pt, Bowtie.apex, toBw]
  · rw [hzpt, toBw_pieceAnc_true hD hq0 hrat (dIdx z)]
    intro heq
    refine z.property.2 ?_
    simpa [Bowtie.pt, Fin.ext_iff, Prod.ext_iff] using heq

/-- **The new points of a stage-2 bowtie are isolated.** -/
theorem frzDist_decor_isolated (z : Decor2 D banc) {w : W ⊕ Decor2 D banc}
    (hw : w ≠ Sum.inr z) :
    (((bsz D banc (dIdx z) : ℕ) : ℝ))⁻¹ ≤ frzDist D banc (Sum.inr z) w := by
  classical
  have hb2 : 2 ≤ bsz D banc (dIdx z) := two_le_bsz (D := D) (banc := banc) (dIdx z)
  have hzpt := toBw_dPos z
  have hs := inv_bsz_le_pieceAnc hD hq0 hrat z
  -- the distances to the other points of its own bowtie
  have hr : ∀ z' : Decor2 D banc, dIdx z' = dIdx z →
      z' = z ∨ (((bsz D banc (dIdx z) : ℕ) : ℝ))⁻¹ ≤
        (if dIdx z = dIdx z' then pieceDist D banc (dIdx z) (dPos z) (dPos z') else 0) := by
    intro z' h
    rw [if_pos h.symm]
    by_cases hval : z'.val.2 = z.val.2
    · exact Or.inl (Subtype.ext (Prod.ext h hval))
    · right
      have hz'b : z'.val.2.1 < bsz D banc (dIdx z) := by
        rw [← h]; exact z'.property.1
      have hz'pt : toBw (bsz D banc (dIdx z)) (dPos z')
          = Bowtie.pt (⟨z'.val.2.1, hz'b⟩ : Fin (bsz D banc (dIdx z))) z'.val.2.2 :=
        toBw_pt (⟨z'.val.2.1, hz'b⟩ : Fin (bsz D banc (dIdx z))) z'.val.2.2
      simp only [pieceDist]
      refine Bowtie.inv_le_bowtie hb2 ?_
      rw [hzpt, hz'pt]
      intro heq
      refine hval ?_
      have h1 : z.val.2.1 = z'.val.2.1 ∧ z.val.2.2 = z'.val.2.2 := by
        simpa [Bowtie.pt, Fin.ext_iff, Prod.ext_iff] using heq
      exact Prod.ext h1.1.symm h1.2.symm
  exact glueFamily_piece_isolated hD (piece_data hD hq0 hrat)
    (inv_bsz_le_one (D := D) (banc := banc) (dIdx z)) z hs hr hw

end

end Stage2
