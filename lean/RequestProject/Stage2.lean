import RequestProject.Bits
import RequestProject.Bowtie
import RequestProject.GlueTransport
import RequestProject.Transport

/-!
# Stage 2 of the canonical extension, on an explicit carrier

`Freeze.lean` glues a finite rigid piece onto every designated pair existentially. Here the
same is done canonically and with a name: the piece glued onto the pair `j` is *the* bowtie
`Bowtie.bowtie (2 * q.den)` for `q = ratOf (D (banc j false) (banc j true))`, its apex sits
at the first anchor and its point of level `2 * q.num` at the second.

The new points are the points of the bowtie other than the two anchors; they are carried by
the subtype `Decor2`, so distinct decoration points are genuinely distinct points at
positive distance (which is what the isolation lemma of Tier 6c needs, and what the
surjection-from-`ℕ` presentation of `Freeze.lean` does not give).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Stage2

open Canonical

variable {W J : Type*}

/-! ### The canonical piece of a target pair -/

/-- The rational distance of the target pair `j`. -/
noncomputable def qOf (D : W → W → ℝ) (banc : J → Bool → W) (j : J) : ℚ :=
  ratOf (D (banc j false) (banc j true))

/-- The size of the bowtie glued onto the target pair `j`. -/
noncomputable def bsz (D : W → W → ℝ) (banc : J → Bool → W) (j : J) : ℕ :=
  2 * (qOf D banc j).den

/-- The level of the bowtie point glued onto the second anchor of the target pair `j`. -/
noncomputable def alv (D : W → W → ℝ) (banc : J → Bool → W) (j : J) : ℕ :=
  2 * (qOf D banc j).num.toNat

/-- The uniform type of abstract piece points: the apex, and the pairs (level, side). -/
abbrev PT : Type := Unit ⊕ (ℕ × Bool)

/-- The abstract piece point `x`, read inside the bowtie `B_b`. -/
def toBw (b : ℕ) : PT → Bowtie.Bw b
  | Sum.inl _ => Bowtie.apex b
  | Sum.inr (n, s) => if h : n < b then Bowtie.pt ⟨n, h⟩ s else Bowtie.apex b

@[simp] theorem toBw_inl (b : ℕ) (u : Unit) : toBw b (Sum.inl u) = Bowtie.apex b := rfl

theorem toBw_pt {b : ℕ} (i : Fin b) (s : Bool) :
    toBw b (Sum.inr ((i : ℕ), s)) = Bowtie.pt i s := by
  simp [toBw, i.isLt]

theorem toBw_surjective (b : ℕ) : Function.Surjective (toBw b) := by
  rintro (u | ⟨i, s⟩)
  · exact ⟨Sum.inl (), rfl⟩
  · exact ⟨Sum.inr ((i : ℕ), s), toBw_pt i s⟩

/-- The metric of the piece glued onto the target `j`, on abstract piece points. -/
noncomputable def pieceDist (D : W → W → ℝ) (banc : J → Bool → W) (j : J) (x y : PT) : ℝ :=
  Bowtie.bowtie (bsz D banc j) (toBw _ x) (toBw _ y)

/-- The two anchors of the piece glued onto the target `j`, as abstract piece points. -/
noncomputable def pieceAnc (D : W → W → ℝ) (banc : J → Bool → W) (j : J) (l : Bool) : PT :=
  if l then Sum.inr (alv D banc j - 1, false) else Sum.inl ()

/-- The new points of stage 2: the points of the bowties other than their two anchors. -/
def Decor2 (D : W → W → ℝ) (banc : J → Bool → W) : Type _ :=
  {y : J × ℕ × Bool // y.2.1 < bsz D banc y.1 ∧ ¬ (y.2.1 = alv D banc y.1 - 1 ∧ y.2.2 = false)}

/-- The piece a stage-2 new point belongs to. -/
def dIdx {D : W → W → ℝ} {banc : J → Bool → W} (y : Decor2 D banc) : J := y.val.1

/-- The abstract piece point carrying a stage-2 new point. -/
def dPos {D : W → W → ℝ} {banc : J → Bool → W} (y : Decor2 D banc) : PT := Sum.inr y.val.2

/-- The stage-2 amalgam: one canonical bowtie glued onto every target pair. -/
noncomputable def frzDist (D : W → W → ℝ) (banc : J → Bool → W) :
    (W ⊕ Decor2 D banc) → (W ⊕ Decor2 D banc) → ℝ :=
  open Classical in
  glueFamily D dIdx banc
    (fun y y' => if dIdx y = dIdx y' then pieceDist D banc (dIdx y) (dPos y) (dPos y') else 0)
    (fun y l => pieceDist D banc (dIdx y) (dPos y) (pieceAnc D banc (dIdx y) l))

/-- The bowtie of the target `j`, placed in the stage-2 amalgam: the apex and the point of
level `alv j` go to the two anchors, every other point is a new point. -/
noncomputable def emb (D : W → W → ℝ) (banc : J → Bool → W) (j : J) :
    PT → (W ⊕ Decor2 D banc)
  | Sum.inl _ => Sum.inl (banc j false)
  | Sum.inr (n, s) =>
      if h : n < bsz D banc j ∧ ¬ (n = alv D banc j - 1 ∧ s = false) then
        Sum.inr ⟨(j, n, s), h.1, h.2⟩
      else if n = alv D banc j - 1 ∧ s = false then Sum.inl (banc j true)
      else Sum.inl (banc j false)

theorem emb_apex (D : W → W → ℝ) (banc : J → Bool → W) (j : J) (u : Unit) :
    emb D banc j (Sum.inl u) = Sum.inl (banc j false) := rfl

theorem emb_new {D : W → W → ℝ} {banc : J → Bool → W} {j : J} {n : ℕ} {s : Bool}
    (h1 : n < bsz D banc j) (h2 : ¬ (n = alv D banc j - 1 ∧ s = false)) :
    emb D banc j (Sum.inr (n, s)) = Sum.inr ⟨(j, n, s), h1, h2⟩ := by
  show (if h : _ then _ else _) = _
  rw [dif_pos ⟨h1, h2⟩]

theorem emb_anchor (D : W → W → ℝ) (banc : J → Bool → W) (j : J) :
    emb D banc j (Sum.inr (alv D banc j - 1, false)) = Sum.inl (banc j true) := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (by tauto), if_pos ⟨rfl, rfl⟩]

theorem emb_far {D : W → W → ℝ} {banc : J → Bool → W} {j : J} {n : ℕ} {s : Bool}
    (h1 : ¬ n < bsz D banc j) (h2 : ¬ (n = alv D banc j - 1 ∧ s = false)) :
    emb D banc j (Sum.inr (n, s)) = Sum.inl (banc j false) := by
  show (if h : _ then _ else _) = _
  rw [dif_neg (by tauto), if_neg h2]

theorem emb_decor {D : W → W → ℝ} {banc : J → Bool → W} (z : Decor2 D banc) :
    emb D banc (dIdx z) (dPos z) = Sum.inr z := by
  obtain ⟨⟨j, n, s⟩, h1, h2⟩ := z
  exact emb_new h1 h2

section

variable {D : W → W → ℝ} {banc : J → Bool → W} (hD : IsBddPseudo D)
  (hq0 : ∀ j, 0 < D (banc j false) (banc j true))
  (hrat : ∀ j, ¬ Irrational (D (banc j false) (banc j true)))

include hD hq0 hrat

omit hD hq0 in
theorem qOf_cast (j : J) : ((qOf D banc j : ℚ) : ℝ) = D (banc j false) (banc j true) :=
  ratOf_spec (hrat j)

omit hD in
theorem qOf_pos (j : J) : 0 < qOf D banc j := by
  have h := qOf_cast hrat j
  have h2 := hq0 j
  rw [← h] at h2
  exact_mod_cast h2

omit hq0 in
theorem qOf_le_one (j : J) : qOf D banc j ≤ 1 := by
  have h := qOf_cast hrat j
  have h1 : D (banc j false) (banc j true) ≤ 1 := hD.le_one _ _
  rw [← h] at h1
  exact_mod_cast h1

omit hD hq0 hrat in
theorem two_le_bsz (j : J) : 2 ≤ bsz D banc j := by
  have := (qOf D banc j).pos
  simp only [bsz]
  omega

omit hD in
theorem one_le_alv (j : J) : 1 ≤ alv D banc j := by
  have h : 0 < (qOf D banc j).num := Rat.num_pos.mpr (qOf_pos hq0 hrat j)
  simp only [alv]
  omega

omit hq0 in
theorem alv_le_bsz (j : J) : alv D banc j ≤ bsz D banc j := by
  have h1 : ((qOf D banc j).num : ℝ) ≤ ((qOf D banc j).den : ℝ) := by
    have h2 : ((qOf D banc j : ℚ) : ℝ) ≤ 1 := by exact_mod_cast qOf_le_one hD hrat j
    have hdenR : (0 : ℝ) < ((qOf D banc j).den : ℝ) := by exact_mod_cast (qOf D banc j).pos
    rw [Rat.cast_def, div_le_one hdenR] at h2
    exact h2
  have h3 : (qOf D banc j).num ≤ ((qOf D banc j).den : ℤ) := by exact_mod_cast h1
  have h4 : (qOf D banc j).num.toNat ≤ (qOf D banc j).den := by omega
  simp only [alv, bsz]
  omega

theorem alv_sub_one_lt_bsz (j : J) : alv D banc j - 1 < bsz D banc j := by
  have := alv_le_bsz hD hrat j
  have := one_le_alv hq0 hrat j
  have := two_le_bsz (D := D) (banc := banc) j
  omega

theorem toBw_pieceAnc_true (j : J) :
    toBw (bsz D banc j) (pieceAnc D banc j true)
      = Bowtie.pt (⟨alv D banc j - 1, alv_sub_one_lt_bsz hD hq0 hrat j⟩ :
          Fin (bsz D banc j)) false := by
  rw [pieceAnc, if_pos rfl]
  exact toBw_pt (⟨alv D banc j - 1, alv_sub_one_lt_bsz hD hq0 hrat j⟩ :
    Fin (bsz D banc j)) false

/-- The bowtie of the target `j` realizes the distance between the two anchors. -/
theorem pieceDist_anc (j : J) :
    pieceDist D banc j (pieceAnc D banc j false) (pieceAnc D banc j true)
      = D (banc j false) (banc j true) := by
  have hb2 : 2 ≤ bsz D banc j := two_le_bsz (D := D) (banc := banc) j
  have ha1 : 1 ≤ alv D banc j := one_le_alv hq0 hrat j
  have hab : alv D banc j ≤ bsz D banc j := alv_le_bsz hD hrat j
  have hidx : alv D banc j - 1 < bsz D banc j := alv_sub_one_lt_bsz hD hq0 hrat j
  have hnumR : (((qOf D banc j).num.toNat : ℕ) : ℝ) = ((qOf D banc j).num : ℝ) := by
    have h : 0 < (qOf D banc j).num := Rat.num_pos.mpr (qOf_pos hq0 hrat j)
    exact_mod_cast Int.toNat_of_nonneg h.le
  have hlvl : Bowtie.lvl (Bowtie.pt (⟨alv D banc j - 1, hidx⟩ : Fin (bsz D banc j)) false)
      = alv D banc j := by
    show (alv D banc j - 1) + 1 = alv D banc j
    omega
  have hne : Bowtie.lvl (Bowtie.apex (bsz D banc j))
      ≠ Bowtie.lvl (Bowtie.pt (⟨alv D banc j - 1, hidx⟩ : Fin (bsz D banc j)) false) := by
    rw [Bowtie.lvl_apex, hlvl]; omega
  have hdenR : (0 : ℝ) < ((qOf D banc j).den : ℝ) := by exact_mod_cast (qOf D banc j).pos
  have habq : ((alv D banc j : ℕ) : ℝ) / ((bsz D banc j : ℕ) : ℝ)
      = ((qOf D banc j : ℚ) : ℝ) := by
    simp only [alv, bsz]
    push_cast
    rw [hnumR, Rat.cast_def]
    field_simp
  simp only [pieceDist]
  rw [toBw_pieceAnc_true hD hq0 hrat j]
  show Bowtie.bowtie (bsz D banc j) (Bowtie.apex (bsz D banc j)) _ = _
  rw [Bowtie.bowtie, Bowtie.raw_of_lvl_ne hne, Bowtie.lvl_apex, hlvl, Nat.cast_zero, zero_sub,
    abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((alv D banc j : ℕ) : ℝ)), habq]
  exact qOf_cast hrat j

omit hD hq0 hrat in
theorem pieceDist_isBddPseudo (j : J) : IsBddPseudo (pieceDist D banc j) :=
  (Bowtie.bowtie_isBddPseudo (two_le_bsz (D := D) (banc := banc) j)).comp (toBw (bsz D banc j))

omit hD hq0 hrat in
theorem pieceDist_rigid (j : J) : Rigid (pieceDist D banc j) :=
  (Bowtie.bowtie_rigid (two_le_bsz (D := D) (banc := banc) j)).comp_surjective (toBw_surjective (bsz D banc j))

theorem piece_compat (j : J) (l l' : Bool) :
    D (banc j l) (banc j l')
      = pieceDist D banc j (pieceAnc D banc j l) (pieceAnc D banc j l') := by
  have hsymm := (pieceDist_isBddPseudo (D := D) (banc := banc) j).symm
  have hdiag := (pieceDist_isBddPseudo (D := D) (banc := banc) j).diag
  cases l <;> cases l'
  · rw [hD.diag, hdiag]
  · exact (pieceDist_anc hD hq0 hrat j).symm
  · rw [hD.symm, hsymm]
    exact (pieceDist_anc hD hq0 hrat j).symm
  · rw [hD.diag, hdiag]

open Classical in
theorem piece_data :
    IsPieceData D (dIdx (D := D) (banc := banc)) banc
      (fun y y' => if dIdx y = dIdx y' then pieceDist D banc (dIdx y) (dPos y) (dPos y') else 0)
      (fun y l => pieceDist D banc (dIdx y) (dPos y) (pieceAnc D banc (dIdx y) l)) := by
  classical
  exact isPieceData_of_uniform D dIdx banc (pieceDist D banc) dPos (pieceAnc D banc)
    (pieceDist_isBddPseudo (D := D) (banc := banc)) (piece_compat hD hq0 hrat)

theorem frzDist_isBddPseudo : IsBddPseudo (frzDist D banc) := by
  classical
  exact glueFamily_isBddPseudo hD (piece_data hD hq0 hrat)

omit hD hq0 hrat in
@[simp] theorem frzDist_base (w w' : W) :
    frzDist D banc (Sum.inl w) (Sum.inl w') = D w w' := rfl

theorem frzDist_locus (z : Decor2 D banc) (l : Bool) :
    frzDist D banc (Sum.inl (banc (dIdx z) l)) (Sum.inr z)
      = pieceDist D banc (dIdx z) (dPos z) (pieceAnc D banc (dIdx z) l) := by
  classical
  exact glueFamily_restrict_locus hD (piece_data hD hq0 hrat) z l

omit hD hq0 hrat in
theorem frzDist_piece {z z' : Decor2 D banc} (h : dIdx z = dIdx z') :
    frzDist D banc (Sum.inr z) (Sum.inr z')
      = pieceDist D banc (dIdx z) (dPos z) (dPos z') := by
  classical
  rw [show frzDist D banc (Sum.inr z) (Sum.inr z') = _ from
    glueFamily_restrict_piece (d := D) (idx := dIdx) h, if_pos h]

/-! ### The bowtie sits isometrically in the amalgam -/

/-- **The glued piece is an isometric copy of its bowtie.** -/
theorem emb_iso (j : J) (x y : PT) :
    frzDist D banc (emb D banc j x) (emb D banc j y) = pieceDist D banc j x y := by
  have key : ∀ x : PT,
      (∃ l : Bool, emb D banc j x = Sum.inl (banc j l) ∧
          toBw (bsz D banc j) (pieceAnc D banc j l) = toBw (bsz D banc j) x) ∨
      (∃ z : Decor2 D banc, emb D banc j x = Sum.inr z ∧ dIdx z = j ∧ dPos z = x) := by
    rintro (u | ⟨n, s⟩)
    · exact Or.inl ⟨false, by cases u; rfl, by cases u; rfl⟩
    · by_cases h2 : n = alv D banc j - 1 ∧ s = false
      · refine Or.inl ⟨true, ?_, ?_⟩
        · obtain ⟨rfl, rfl⟩ := h2
          exact emb_anchor D banc j
        · obtain ⟨rfl, rfl⟩ := h2
          rw [pieceAnc, if_pos rfl]
      · by_cases h1 : n < bsz D banc j
        · exact Or.inr ⟨⟨(j, n, s), h1, h2⟩, emb_new h1 h2, rfl, rfl⟩
        · refine Or.inl ⟨false, emb_far h1 h2, ?_⟩
          rw [pieceAnc, if_neg (by simp)]
          simp [toBw, h1]
  have hbdd := frzDist_isBddPseudo hD hq0 hrat (banc := banc)
  rcases key x with ⟨l, hx, hx'⟩ | ⟨z, hx, hzj, hx'⟩ <;>
    rcases key y with ⟨l', hy, hy'⟩ | ⟨z', hy, hzj', hy'⟩
  · rw [hx, hy, frzDist_base, piece_compat hD hq0 hrat j l l']
    simp only [pieceDist, hx', hy']
  · rw [hx, hy, ← hzj', frzDist_locus hD hq0 hrat z' l, hzj']
    simp only [pieceDist, hx', hy']
    exact (Bowtie.bowtie_isBddPseudo (two_le_bsz (D := D) (banc := banc) j)).symm _ _
  · rw [hx, hy, hbdd.symm, ← hzj, frzDist_locus hD hq0 hrat z l', hzj]
    simp only [pieceDist, hx', hy']
  · rw [hx, hy, frzDist_piece (hzj.trans hzj'.symm), hzj]
    simp only [pieceDist, hx', hy']

/-- **Every perturbation of the stage-2 amalgam vanishes on the glued bowties.** -/
theorem frz_pert_piece (E : (W ⊕ Decor2 D banc) → (W ⊕ Decor2 D banc) → ℝ)
    (hE : IsPerturbation (frzDist D banc) E) (j : J) :
    ∀ x y : PT, E (emb D banc j x) (emb D banc j y) = 0 :=
  pert_eq_zero_of_isometry hE (pieceDist_rigid (D := D) (banc := banc) j) (emb D banc j)
    (emb_iso hD hq0 hrat j)

/-- **The target pairs are frozen.** -/
theorem frz_pert_target (E : (W ⊕ Decor2 D banc) → (W ⊕ Decor2 D banc) → ℝ)
    (hE : IsPerturbation (frzDist D banc) E) (j : J) :
    E (Sum.inl (banc j false)) (Sum.inl (banc j true)) = 0 := by
  have h := frz_pert_piece hD hq0 hrat E hE j (Sum.inl ())
    (Sum.inr (alv D banc j - 1, false))
  rwa [emb_apex, emb_anchor] at h

/-- A perturbation vanishes between a new point and the anchors of its own piece. -/
theorem frz_pert_anchor (E : (W ⊕ Decor2 D banc) → (W ⊕ Decor2 D banc) → ℝ)
    (hE : IsPerturbation (frzDist D banc) E) (z : Decor2 D banc) (l : Bool) :
    E (Sum.inl (banc (dIdx z) l)) (Sum.inr z) = 0 := by
  have h := frz_pert_piece hD hq0 hrat E hE (dIdx z) (pieceAnc D banc (dIdx z) l) (dPos z)
  rwa [emb_decor z, show emb D banc (dIdx z) (pieceAnc D banc (dIdx z) l)
      = Sum.inl (banc (dIdx z) l) from by
    cases l
    · rw [pieceAnc, if_neg (by simp)]; rfl
    · rw [pieceAnc, if_pos rfl]; exact emb_anchor D banc (dIdx z)] at h

/-- A perturbation of the stage-2 amalgam vanishing on the base vanishes identically. -/
theorem frz_pert_transfer (E : (W ⊕ Decor2 D banc) → (W ⊕ Decor2 D banc) → ℝ)
    (hE : IsPerturbation (frzDist D banc) E)
    (hbase : ∀ w w', E (Sum.inl w) (Sum.inl w') = 0) : ∀ x y, E x y = 0 := by
  classical
  have hp := piece_data hD hq0 hrat (banc := banc)
  set D' := frzDist D banc with hD'
  have hanc := frz_pert_anchor hD hq0 hrat E hE
  -- two new points of the same piece
  have hsame : ∀ (z z' : Decor2 D banc), dIdx z = dIdx z' → E (Sum.inr z) (Sum.inr z') = 0 := by
    intro z z' h
    have hz := emb_decor z
    have hz' : emb D banc (dIdx z) (dPos z') = Sum.inr z' := by
      rw [h]; exact emb_decor z'
    have := frz_pert_piece hD hq0 hrat E hE (dIdx z) (dPos z) (dPos z')
    rwa [hz, hz'] at this
  -- base to new point
  have hcross : ∀ (w : W) (z : Decor2 D banc), E (Sum.inl w) (Sum.inr z) = 0 := by
    intro w z
    rcases glueFamily_dichotomy_base_piece hD hp w z with h1 | ⟨l, h1⟩
    · exact pert_eq_zero_of_dist_eq_one hE h1
    · rw [pert_add_of_tight D' E hE h1, hbase, hanc z l, add_zero]
  rintro (w | z) (w' | z')
  · exact hbase w w'
  · exact hcross w z'
  · rw [hE.1]; exact hcross w' z
  · by_cases hjj : dIdx z = dIdx z'
    · exact hsame z z' hjj
    · rcases glueFamily_dichotomy_piece_piece hD hp hjj with h1 | ⟨l, l', h1⟩
      · exact pert_eq_zero_of_dist_eq_one hE h1
      · set q : ℕ → (W ⊕ Decor2 D banc) := fun k =>
          match k with
          | 0 => Sum.inr z
          | 1 => Sum.inl (banc (dIdx z) l)
          | 2 => Sum.inl (banc (dIdx z') l')
          | _ => Sum.inr z' with hq
        have htight : D' (q 0) (q 3) = ∑ i ∈ Finset.range 3, D' (q i) (q (i + 1)) := by
          simp only [hq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          simpa using h1
        have hsum := pert_add_of_tight_chain D' E hE (m := 3) q htight
        have e0 : E (q 0) (q 1) = 0 := by
          simp only [hq]
          rw [hE.1]
          exact hanc z l
        have e1 : E (q 1) (q 2) = 0 := by simp only [hq]; exact hbase _ _
        have e2 : E (q 2) (q 3) = 0 := by simp only [hq]; exact hanc z' l'
        have hz : E (q 0) (q 3) = 0 := by
          rw [hsum]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          rw [e0, e1, e2]; ring
        simpa [hq] using hz

end

end Stage2
