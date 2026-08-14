import RequestProject.GlueFamily

/-!
# Transport of the family amalgam, and uniform piece data

Two additions to the Tier 4 gluing machinery, both needed by the canonical extension of
Tier 6 and both stated for the *explicit carrier* `X ⊕ Y` of `glueFamily`.

* `glueFamily_transport`: a map of gluing data — an isometry `fX` of the bases, an
  injection `fI` of the index sets and a map `fY` of the new points matching pieces with
  pieces — induces an isometry of the amalgams. This is the engine of functoriality
  (paper Theorem 6.3).
* `isPieceData_of_uniform`: piece data assembled from a family of bounded-by-one
  pseudometrics `m i` on a *common* type `PT` of abstract piece points, with `pos` placing
  each new point and `anc` placing the anchors. This is the shape in which the bowtie
  pieces of stage 2 are presented.
-/

set_option autoImplicit false

variable {X Y I L X' Y' I' : Type*}

/-! ### Transport -/

theorem gfBasePiece_transport [Fintype L] [Nonempty L]
    {d : X → X → ℝ} {idx : Y → I} {g : I → L → X} {s : Y → L → ℝ}
    {d' : X' → X' → ℝ} {idx' : Y' → I'} {g' : I' → L → X'} {s' : Y' → L → ℝ}
    {fX : X → X'} {fY : Y → Y'} {fI : I → I'}
    (hfX : ∀ x y, d' (fX x) (fX y) = d x y)
    (hidx : ∀ y, idx' (fY y) = fI (idx y))
    (hg : ∀ i l, g' (fI i) l = fX (g i l))
    (hs : ∀ y l, s' (fY y) l = s y l) (x : X) (y : Y) :
    gfBasePiece d' idx' g' s' (fX x) (fY y) = gfBasePiece d idx g s x y := by
  have h : (fun l => d' (fX x) (g' (idx' (fY y)) l) + s' (fY y) l)
      = (fun l => d x (g (idx y) l) + s y l) := by
    funext l; rw [hidx, hg, hfX, hs]
  rw [gfBasePiece, gfBasePiece, h]

theorem gfPiecePiece_transport [Fintype L] [Nonempty L]
    {d : X → X → ℝ} {idx : Y → I} {g : I → L → X} {s : Y → L → ℝ}
    {d' : X' → X' → ℝ} {idx' : Y' → I'} {g' : I' → L → X'} {s' : Y' → L → ℝ}
    {fX : X → X'} {fY : Y → Y'} {fI : I → I'}
    (hfX : ∀ x y, d' (fX x) (fX y) = d x y)
    (hidx : ∀ y, idx' (fY y) = fI (idx y))
    (hg : ∀ i l, g' (fI i) l = fX (g i l))
    (hs : ∀ y l, s' (fY y) l = s y l) (y y' : Y) :
    gfPiecePiece d' idx' g' s' (fY y) (fY y') = gfPiecePiece d idx g s y y' := by
  have h : (fun l => s' (fY y) l + gfBasePiece d' idx' g' s' (g' (idx' (fY y)) l) (fY y'))
      = (fun l => s y l + gfBasePiece d idx g s (g (idx y) l) y') := by
    funext l
    rw [hidx, hg, hs, gfBasePiece_transport hfX hidx hg hs]
  rw [gfPiecePiece, gfPiecePiece, h]

/-- **Transport of the family amalgam along a map of gluing data.** An isometry of the
bases together with an injection of the index sets and a piecewise-matching map of the new
points induces an isometry `Sum.map fX fY` of the amalgams. -/
theorem glueFamily_transport [Fintype L] [Nonempty L] [DecidableEq I] [DecidableEq I']
    {d : X → X → ℝ} {idx : Y → I} {g : I → L → X} {r : Y → Y → ℝ} {s : Y → L → ℝ}
    {d' : X' → X' → ℝ} {idx' : Y' → I'} {g' : I' → L → X'} {r' : Y' → Y' → ℝ}
    {s' : Y' → L → ℝ} {fX : X → X'} {fY : Y → Y'} {fI : I → I'}
    (hfX : ∀ x y, d' (fX x) (fX y) = d x y)
    (hidx : ∀ y, idx' (fY y) = fI (idx y))
    (hfI : Function.Injective fI)
    (hg : ∀ i l, g' (fI i) l = fX (g i l))
    (hr : ∀ y y', idx y = idx y' → r' (fY y) (fY y') = r y y')
    (hs : ∀ y l, s' (fY y) l = s y l) :
    ∀ a b : X ⊕ Y, glueFamily d' idx' g' r' s' (Sum.map fX fY a) (Sum.map fX fY b)
      = glueFamily d idx g r s a b := by
  rintro (x | y) (x' | y')
  · exact hfX x x'
  · simp only [Sum.map_inl, Sum.map_inr, glueFamily_inl_inr,
      gfBasePiece_transport hfX hidx hg hs]
  · simp only [Sum.map_inl, Sum.map_inr, glueFamily_inr_inl,
      gfBasePiece_transport hfX hidx hg hs]
  · simp only [Sum.map_inr, glueFamily_inr_inr, hidx]
    by_cases h : idx y = idx y'
    · rw [if_pos (by rw [h]), if_pos h, hr y y' h]
    · rw [if_neg (fun hc => h (hfI hc)), if_neg h,
        gfPiecePiece_transport hfX hidx hg hs]

/-! ### Uniform piece data -/

/-- Piece data assembled from a uniform family of bounded-by-one pseudometrics: `m i` is the
metric of the piece `i` on a common type `PT` of abstract piece points, `pos y` is the point
of `PT` carrying the new point `y`, and `anc i` places the anchors of the piece `i`. -/
theorem isPieceData_of_uniform {W PT : Type*} [DecidableEq I] (D : W → W → ℝ)
    (idx : Y → I) (g : I → L → W) (m : I → PT → PT → ℝ) (pos : Y → PT) (anc : I → L → PT)
    (hm : ∀ i, IsBddPseudo (m i))
    (hcompat : ∀ i l l', D (g i l) (g i l') = m i (anc i l) (anc i l')) :
    IsPieceData D idx g (fun y y' => if idx y = idx y' then m (idx y) (pos y) (pos y') else 0)
      (fun y l => m (idx y) (pos y) (anc (idx y) l)) where
  r_nonneg y y' := by
    split
    · exact (hm _).nonneg _ _
    · exact le_rfl
  r_le_one y y' := by
    split
    · exact (hm _).le_one _ _
    · exact zero_le_one
  r_diag y := by simp [(hm (idx y)).diag]
  r_symm y y' := by
    by_cases h : idx y = idx y'
    · rw [if_pos h, if_pos h.symm, ← h, (hm (idx y)).symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  s_nonneg y l := (hm _).nonneg _ _
  s_le_one y l := (hm _).le_one _ _
  tri_rrr y y' y'' h1 h2 := by
    rw [if_pos (h1.trans h2), if_pos h1, if_pos h2, ← h1]
    exact (hm (idx y)).triangle _ _ _
  tri_rrs y y' l h := by
    rw [if_pos h, ← h]
    exact (hm (idx y)).triangle _ _ _
  tri_ssr y y' l h := by
    rw [if_pos h, ← h]
    have h1 := (hm (idx y)).triangle (pos y) (anc (idx y) l) (pos y')
    have h2 := (hm (idx y)).symm (anc (idx y) l) (pos y')
    linarith
  tri_ssd y l l' := by
    rw [hcompat]
    exact (hm (idx y)).triangle _ _ _
  tri_dss y l l' := by
    rw [hcompat]
    have h1 := (hm (idx y)).triangle (anc (idx y) l) (pos y) (anc (idx y) l')
    have h2 := (hm (idx y)).symm (anc (idx y) l) (pos y)
    linarith
