import RequestProject.Chain

/-!
# Tier 4b: gluing a family of pieces along finite loci in a common base

`Glue.lean` amalgamates a base with *one* piece along a finite locus. Here the same
construction is carried out for an indexed family of pieces, all glued to a common base
`(X, d)`.

## The data

To avoid dependent types (a family of piece carriers `P : I → Type*` forces `Sigma`
gymnastics in every proof) the pieces are described by *uniform* data:

* `Y` is the type of all new points and `idx : Y → I` says which piece a new point
  belongs to;
* `L` is the (finite, nonempty) locus type, the same for every piece, and `g : I → L → X`
  places the locus of piece `i` inside the base;
* `r : Y → Y → ℝ` gives the distance between two new points *of the same piece*, and
  `s : Y → L → ℝ` the distance from a new point to a locus point of its own piece.

`IsPieceData d idx g r s` says exactly that, for every `i`, these data assemble into a
bounded-by-one pseudometric on `{y // idx y = i} ⊕ L` whose restriction to `L` is the
distance `d` between the locus points — the hypothesis `d|_{F×F} = ρ|_{F×F}` of the paper's
Lemma 3.1, here built into the shape of the data.

## The construction

`glueFamily d idx g r s` is the truncation at `1` of the "amalgamated" distance: base to
base is `d`; base to piece point is the minimum over the locus of the two-leg path; two
points of the same piece keep their piece distance `r`; two points of different pieces are
joined by the minimum over both loci of the three-leg path.
-/

set_option autoImplicit false

open scoped BigOperators

variable {X Y I L : Type*}

/-- The data of a family of pieces glued to `(X, d)` along the loci `g i : L → X`. It says
that for each index `i` the functions `r`, `s` and `d` assemble into a bounded-by-one
pseudometric on (the new points of piece `i`) `⊕ L`. -/
structure IsPieceData (d : X → X → ℝ) (idx : Y → I) (g : I → L → X)
    (r : Y → Y → ℝ) (s : Y → L → ℝ) : Prop where
  r_nonneg : ∀ y y', 0 ≤ r y y'
  r_le_one : ∀ y y', r y y' ≤ 1
  r_diag : ∀ y, r y y = 0
  r_symm : ∀ y y', r y y' = r y' y
  s_nonneg : ∀ y l, 0 ≤ s y l
  s_le_one : ∀ y l, s y l ≤ 1
  /-- Triangle inequality for three new points of the same piece. -/
  tri_rrr : ∀ y y' y'', idx y = idx y' → idx y' = idx y'' → r y y'' ≤ r y y' + r y' y''
  /-- Triangle inequality for two new points of a piece and a locus point. -/
  tri_rrs : ∀ y y' l, idx y = idx y' → s y l ≤ r y y' + s y' l
  /-- Triangle inequality for two new points of a piece and a locus point. -/
  tri_ssr : ∀ y y' l, idx y = idx y' → r y y' ≤ s y l + s y' l
  /-- Triangle inequality for a new point and two locus points. -/
  tri_ssd : ∀ y l l', s y l ≤ s y l' + d (g (idx y) l') (g (idx y) l)
  /-- Triangle inequality for a new point and two locus points. -/
  tri_dss : ∀ y l l', d (g (idx y) l) (g (idx y) l') ≤ s y l + s y l'

section Defs

variable [Fintype L] [Nonempty L]

/-- The base-to-piece distance before truncation: the shortest two-leg path through the
locus of the piece. -/
noncomputable def gfBasePiece (d : X → X → ℝ) (idx : Y → I) (g : I → L → X) (s : Y → L → ℝ)
    (x : X) (y : Y) : ℝ :=
  (Finset.univ : Finset L).inf' Finset.univ_nonempty fun l => d x (g (idx y) l) + s y l

/-- The piece-to-piece distance before truncation: the shortest three-leg path through the
two loci. -/
noncomputable def gfPiecePiece (d : X → X → ℝ) (idx : Y → I) (g : I → L → X) (s : Y → L → ℝ)
    (y y' : Y) : ℝ :=
  (Finset.univ : Finset L).inf' Finset.univ_nonempty fun l =>
    s y l + gfBasePiece d idx g s (g (idx y) l) y'

/-- The amalgam of the family of pieces with the base, truncated at `1`. -/
noncomputable def glueFamily [DecidableEq I] (d : X → X → ℝ) (idx : Y → I) (g : I → L → X)
    (r : Y → Y → ℝ) (s : Y → L → ℝ) : (X ⊕ Y) → (X ⊕ Y) → ℝ
  | Sum.inl x, Sum.inl x' => d x x'
  | Sum.inl x, Sum.inr y => min 1 (gfBasePiece d idx g s x y)
  | Sum.inr y, Sum.inl x => min 1 (gfBasePiece d idx g s x y)
  | Sum.inr y, Sum.inr y' =>
      if idx y = idx y' then r y y' else min 1 (gfPiecePiece d idx g s y y')

end Defs

section Basic

variable [Fintype L] [Nonempty L] {d : X → X → ℝ} {idx : Y → I} {g : I → L → X}
  {r : Y → Y → ℝ} {s : Y → L → ℝ}

theorem gfBasePiece_le (x : X) (y : Y) (l : L) :
    gfBasePiece d idx g s x y ≤ d x (g (idx y) l) + s y l :=
  Finset.inf'_le _ (Finset.mem_univ l)

theorem gfBasePiece_exists (x : X) (y : Y) :
    ∃ l : L, gfBasePiece d idx g s x y = d x (g (idx y) l) + s y l := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := L))
    (fun l => d x (g (idx y) l) + s y l)
  exact ⟨l, hl⟩

theorem gfPiecePiece_le (y y' : Y) (l l' : L) :
    gfPiecePiece d idx g s y y' ≤
      s y l + d (g (idx y) l) (g (idx y') l') + s y' l' := by
  have h1 : gfPiecePiece d idx g s y y' ≤ s y l + gfBasePiece d idx g s (g (idx y) l) y' :=
    Finset.inf'_le _ (Finset.mem_univ l)
  have h2 := gfBasePiece_le (d := d) (idx := idx) (g := g) (s := s) (g (idx y) l) y' l'
  linarith

theorem gfPiecePiece_exists (y y' : Y) :
    ∃ l l' : L, gfPiecePiece d idx g s y y' =
      s y l + d (g (idx y) l) (g (idx y') l') + s y' l' := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := L))
    (fun l => s y l + gfBasePiece d idx g s (g (idx y) l) y')
  obtain ⟨l', hl'⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s)
    (g (idx y) l) y'
  exact ⟨l, l', by rw [gfPiecePiece, hl, hl']; ring⟩

theorem gfBasePiece_nonneg (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s)
    (x : X) (y : Y) : 0 ≤ gfBasePiece d idx g s x y := by
  refine Finset.le_inf' _ _ fun l _ => ?_
  exact add_nonneg (hd.nonneg _ _) (hp.s_nonneg _ _)

theorem gfPiecePiece_nonneg (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s)
    (y y' : Y) : 0 ≤ gfPiecePiece d idx g s y y' := by
  refine Finset.le_inf' _ _ fun l _ => ?_
  exact add_nonneg (hp.s_nonneg _ _) (gfBasePiece_nonneg hd hp _ _)

theorem gfPiecePiece_symm (hd : IsBddPseudo d) (y y' : Y) :
    gfPiecePiece d idx g s y y' = gfPiecePiece d idx g s y' y := by
  have key : ∀ a b : Y, gfPiecePiece d idx g s a b ≤ gfPiecePiece d idx g s b a := by
    intro a b
    obtain ⟨l, l', hl⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s) b a
    have := gfPiecePiece_le (d := d) (idx := idx) (g := g) (s := s) a b l' l
    rw [hl]
    rw [hd.symm (g (idx a) l') (g (idx b) l)] at this
    linarith
  exact le_antisymm (key y y') (key y' y)

end Basic

section Restrict

variable [Fintype L] [Nonempty L] [DecidableEq I] {d : X → X → ℝ} {idx : Y → I}
  {g : I → L → X} {r : Y → Y → ℝ} {s : Y → L → ℝ}

@[simp] theorem glueFamily_inl_inl (x x' : X) :
    glueFamily d idx g r s (Sum.inl x) (Sum.inl x') = d x x' := rfl

@[simp] theorem glueFamily_inl_inr (x : X) (y : Y) :
    glueFamily d idx g r s (Sum.inl x) (Sum.inr y) = min 1 (gfBasePiece d idx g s x y) := rfl

@[simp] theorem glueFamily_inr_inl (y : Y) (x : X) :
    glueFamily d idx g r s (Sum.inr y) (Sum.inl x) = min 1 (gfBasePiece d idx g s x y) := rfl

theorem glueFamily_inr_inr (y y' : Y) :
    glueFamily d idx g r s (Sum.inr y) (Sum.inr y') =
      if idx y = idx y' then r y y' else min 1 (gfPiecePiece d idx g s y y') := rfl

/-- **The base sits isometrically in the amalgam.** -/
theorem glueFamily_restrict_base (x x' : X) :
    glueFamily d idx g r s (Sum.inl x) (Sum.inl x') = d x x' := rfl

/-- **Each piece sits isometrically in the amalgam**, part one: two new points of the same
piece keep their distance. -/
theorem glueFamily_restrict_piece {y y' : Y} (h : idx y = idx y') :
    glueFamily d idx g r s (Sum.inr y) (Sum.inr y') = r y y' := by
  rw [glueFamily_inr_inr, if_pos h]

/-- **Each piece sits isometrically in the amalgam**, part two: a new point keeps its
distance to the locus of its own piece. -/
theorem glueFamily_restrict_locus (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s)
    (y : Y) (l : L) :
    glueFamily d idx g r s (Sum.inl (g (idx y) l)) (Sum.inr y) = s y l := by
  have hle : gfBasePiece d idx g s (g (idx y) l) y ≤ s y l := by
    have := gfBasePiece_le (d := d) (idx := idx) (g := g) (s := s) (g (idx y) l) y l
    rw [hd.diag] at this
    linarith
  have hge : s y l ≤ gfBasePiece d idx g s (g (idx y) l) y := by
    refine Finset.le_inf' _ _ fun l' _ => ?_
    have := hp.tri_ssd y l l'
    rw [hd.symm (g (idx y) l) (g (idx y) l')]
    linarith
  have heq : gfBasePiece d idx g s (g (idx y) l) y = s y l := le_antisymm hle hge
  rw [glueFamily_inl_inr, heq, min_eq_right (hp.s_le_one y l)]

end Restrict

section Triangle

variable [Fintype L] [Nonempty L] [DecidableEq I] {d : X → X → ℝ} {idx : Y → I}
  {g : I → L → X} {r : Y → Y → ℝ} {s : Y → L → ℝ}
  (hd : IsBddPseudo d) (hp : IsPieceData d idx g r s)

include hd hp

omit [DecidableEq I] hp in
/-- Triangle `(base, base, piece)`. -/
theorem gf_tri_BBP (x x' : X) (y : Y) :
    min 1 (gfBasePiece d idx g s x y) ≤ d x x' + min 1 (gfBasePiece d idx g s x' y) := by
  rcases min_cases 1 (gfBasePiece d idx g s x' y) with ⟨he, hle⟩ | ⟨he, hlt⟩
  · rw [he]
    have := min_le_left 1 (gfBasePiece d idx g s x y)
    have := hd.nonneg x x'
    linarith
  · rw [he]
    obtain ⟨l, hl⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x' y
    have h1 := gfBasePiece_le (d := d) (idx := idx) (g := g) (s := s) x y l
    have h2 : d x (g (idx y) l) ≤ d x x' + d x' (g (idx y) l) := hd.triangle _ _ _
    have h3 := min_le_right 1 (gfBasePiece d idx g s x y)
    rw [hl]
    linarith

omit [DecidableEq I] in
/-- Triangle `(base, piece, base)`. -/
theorem gf_tri_BPB (x x' : X) (y : Y) :
    d x x' ≤ min 1 (gfBasePiece d idx g s x y) + min 1 (gfBasePiece d idx g s x' y) := by
  rcases min_cases 1 (gfBasePiece d idx g s x y) with ⟨he, hle⟩ | ⟨he, hlt⟩
  · rw [he]
    have := hd.le_one x x'
    have : (0:ℝ) ≤ min 1 (gfBasePiece d idx g s x' y) :=
      le_min zero_le_one (gfBasePiece_nonneg hd hp x' y)
    linarith [hd.le_one x x']
  rcases min_cases 1 (gfBasePiece d idx g s x' y) with ⟨he', hle'⟩ | ⟨he', hlt'⟩
  · rw [he']
    have : (0:ℝ) ≤ min 1 (gfBasePiece d idx g s x y) :=
      le_min zero_le_one (gfBasePiece_nonneg hd hp x y)
    linarith [hd.le_one x x']
  · rw [he, he']
    obtain ⟨l, hl⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x y
    obtain ⟨l', hl'⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x' y
    rw [hl, hl']
    have t1 : d x x' ≤ d x (g (idx y) l) + d (g (idx y) l) x' := hd.triangle _ _ _
    have t2 : d (g (idx y) l) x' ≤ d (g (idx y) l) (g (idx y) l') + d (g (idx y) l') x' :=
      hd.triangle _ _ _
    have t3 := hp.tri_dss y l l'
    have e : d (g (idx y) l') x' = d x' (g (idx y) l') := hd.symm _ _
    linarith

/-- Triangle `(base, piece, piece)`. -/
theorem gf_tri_BPP (x : X) (y y' : Y) :
    min 1 (gfBasePiece d idx g s x y') ≤
      min 1 (gfBasePiece d idx g s x y) + glueFamily d idx g r s (Sum.inr y) (Sum.inr y') := by
  have hone : min 1 (gfBasePiece d idx g s x y') ≤ 1 := min_le_left _ _
  rcases min_cases 1 (gfBasePiece d idx g s x y) with ⟨he, hle⟩ | ⟨he, hlt⟩
  · rw [he]
    have : 0 ≤ glueFamily d idx g r s (Sum.inr y) (Sum.inr y') := by
      rw [glueFamily_inr_inr]
      split
      · exact hp.r_nonneg _ _
      · exact le_min zero_le_one (gfPiecePiece_nonneg hd hp y y')
    linarith
  obtain ⟨l, hl⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x y
  by_cases hij : idx y = idx y'
  · rw [glueFamily_restrict_piece hij, he, hl]
    have h1 := gfBasePiece_le (d := d) (idx := idx) (g := g) (s := s) x y' l
    have h2 : s y' l ≤ r y' y + s y l := hp.tri_rrs y' y l hij.symm
    have h3 : r y' y = r y y' := hp.r_symm _ _
    have h4 := min_le_right 1 (gfBasePiece d idx g s x y')
    rw [hij] at hl ⊢
    linarith
  · rw [glueFamily_inr_inr, if_neg hij, he]
    rcases min_cases 1 (gfPiecePiece d idx g s y y') with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]
      have : (0:ℝ) ≤ gfBasePiece d idx g s x y := gfBasePiece_nonneg hd hp x y
      linarith
    · rw [hm]
      obtain ⟨m, m', hmm⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s) y y'
      rw [hmm, hl]
      have h1 := gfBasePiece_le (d := d) (idx := idx) (g := g) (s := s) x y' m'
      have h2 : d x (g (idx y') m') ≤ d x (g (idx y) l) + d (g (idx y) l) (g (idx y') m') :=
        hd.triangle _ _ _
      have h3 : d (g (idx y) l) (g (idx y') m') ≤
          d (g (idx y) l) (g (idx y) m) + d (g (idx y) m) (g (idx y') m') := hd.triangle _ _ _
      have h4 := hp.tri_dss y l m
      have h5 := min_le_right 1 (gfBasePiece d idx g s x y')
      linarith

/-- Triangle `(piece, base, piece)`. -/
theorem gf_tri_PBP (x : X) (y y' : Y) :
    glueFamily d idx g r s (Sum.inr y) (Sum.inr y') ≤
      min 1 (gfBasePiece d idx g s x y) + min 1 (gfBasePiece d idx g s x y') := by
  rcases min_cases 1 (gfBasePiece d idx g s x y) with ⟨he, hle⟩ | ⟨he, hlt⟩
  · rw [he]
    have h0 : (0:ℝ) ≤ min 1 (gfBasePiece d idx g s x y') :=
      le_min zero_le_one (gfBasePiece_nonneg hd hp x y')
    have h1 : glueFamily d idx g r s (Sum.inr y) (Sum.inr y') ≤ 1 := by
      rw [glueFamily_inr_inr]
      split
      · exact hp.r_le_one _ _
      · exact min_le_left _ _
    linarith
  rcases min_cases 1 (gfBasePiece d idx g s x y') with ⟨he', hle'⟩ | ⟨he', hlt'⟩
  · rw [he']
    have h0 : (0:ℝ) ≤ min 1 (gfBasePiece d idx g s x y) :=
      le_min zero_le_one (gfBasePiece_nonneg hd hp x y)
    have h1 : glueFamily d idx g r s (Sum.inr y) (Sum.inr y') ≤ 1 := by
      rw [glueFamily_inr_inr]
      split
      · exact hp.r_le_one _ _
      · exact min_le_left _ _
    linarith
  rw [he, he']
  obtain ⟨l, hl⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x y
  obtain ⟨l', hl'⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x y'
  rw [hl, hl']
  by_cases hij : idx y = idx y'
  · rw [glueFamily_restrict_piece hij]
    have hgg : ∀ m : L, g (idx y') m = g (idx y) m := fun m => by rw [hij]
    have h1 : r y y' ≤ s y l + s y' l := hp.tri_ssr y y' l hij
    have h2 : s y' l ≤ s y' l' + d (g (idx y) l') (g (idx y) l) := by
      have := hp.tri_ssd y' l l'
      rwa [hgg, hgg] at this
    have h3 : d (g (idx y) l') (g (idx y) l) ≤
        d (g (idx y) l') x + d x (g (idx y) l) := hd.triangle _ _ _
    have e1 : d (g (idx y) l') x = d x (g (idx y) l') := hd.symm _ _
    rw [hgg l']
    linarith
  · rw [glueFamily_inr_inr, if_neg hij]
    have h1 := gfPiecePiece_le (d := d) (idx := idx) (g := g) (s := s) y y' l l'
    have h2 : d (g (idx y) l) (g (idx y') l') ≤
        d (g (idx y) l) x + d x (g (idx y') l') := hd.triangle _ _ _
    have e1 : d (g (idx y) l) x = d x (g (idx y) l) := hd.symm _ _
    have h3 := min_le_right 1 (gfPiecePiece d idx g s y y')
    linarith

/-- Triangle `(piece, piece, piece)`. -/
theorem gf_tri_PPP (y y' y'' : Y) :
    glueFamily d idx g r s (Sum.inr y) (Sum.inr y'') ≤
      glueFamily d idx g r s (Sum.inr y) (Sum.inr y') +
        glueFamily d idx g r s (Sum.inr y') (Sum.inr y'') := by
  have hnn : ∀ a b : Y, 0 ≤ glueFamily d idx g r s (Sum.inr a) (Sum.inr b) := by
    intro a b
    rw [glueFamily_inr_inr]
    split
    · exact hp.r_nonneg _ _
    · exact le_min zero_le_one (gfPiecePiece_nonneg hd hp a b)
  have hle1 : ∀ a b : Y, glueFamily d idx g r s (Sum.inr a) (Sum.inr b) ≤ 1 := by
    intro a b
    rw [glueFamily_inr_inr]
    split
    · exact hp.r_le_one _ _
    · exact min_le_left _ _
  by_cases h1 : idx y = idx y'
  · by_cases h2 : idx y' = idx y''
    · -- all three in the same piece
      rw [glueFamily_restrict_piece (h1.trans h2), glueFamily_restrict_piece h1,
        glueFamily_restrict_piece h2]
      exact hp.tri_rrr y y' y'' h1 h2
    · -- y, y' in one piece, y'' in another
      have h3 : idx y ≠ idx y'' := by rw [h1]; exact h2
      rw [glueFamily_restrict_piece h1, glueFamily_inr_inr, if_neg h3, glueFamily_inr_inr,
        if_neg h2]
      rcases min_cases 1 (gfPiecePiece d idx g s y' y'') with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]
        have := hp.r_nonneg y y'
        have := hle1 y y''
        rw [glueFamily_inr_inr, if_neg h3] at this
        linarith
      · rw [he]
        obtain ⟨m, m'', hm⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s)
          y' y''
        rw [hm]
        have hle := gfPiecePiece_le (d := d) (idx := idx) (g := g) (s := s) y y'' m m''
        have hs : s y m ≤ r y y' + s y' m := hp.tri_rrs y y' m h1
        have heq : g (idx y) m = g (idx y') m := by rw [h1]
        have hmin := min_le_right 1 (gfPiecePiece d idx g s y y'')
        rw [heq] at hle
        linarith
  · by_cases h2 : idx y' = idx y''
    · -- y in one piece, y', y'' in another
      have h3 : idx y ≠ idx y'' := by rw [← h2]; exact h1
      rw [glueFamily_restrict_piece h2, glueFamily_inr_inr, if_neg h3, glueFamily_inr_inr,
        if_neg h1]
      rcases min_cases 1 (gfPiecePiece d idx g s y y') with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]
        have := hp.r_nonneg y' y''
        have := hle1 y y''
        rw [glueFamily_inr_inr, if_neg h3] at this
        linarith
      · rw [he]
        obtain ⟨m, m', hm⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s) y y'
        rw [hm]
        have hle := gfPiecePiece_le (d := d) (idx := idx) (g := g) (s := s) y y'' m m'
        have hs : s y'' m' ≤ r y'' y' + s y' m' := hp.tri_rrs y'' y' m' h2.symm
        have hsymm : r y'' y' = r y' y'' := hp.r_symm _ _
        have heq : g (idx y'') m' = g (idx y') m' := by rw [h2]
        have hmin := min_le_right 1 (gfPiecePiece d idx g s y y'')
        rw [heq] at hle
        linarith
    · -- y and y' in different pieces, y' and y'' in different pieces
      rw [glueFamily_inr_inr (y := y) (y' := y'), if_neg h1,
        glueFamily_inr_inr (y := y') (y' := y''), if_neg h2]
      rcases min_cases 1 (gfPiecePiece d idx g s y y') with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he]
        have h0 : (0:ℝ) ≤ min 1 (gfPiecePiece d idx g s y' y'') :=
          le_min zero_le_one (gfPiecePiece_nonneg hd hp y' y'')
        have := hle1 y y''
        linarith
      rcases min_cases 1 (gfPiecePiece d idx g s y' y'') with ⟨he', -⟩ | ⟨he', -⟩
      · rw [he']
        have h0 : (0:ℝ) ≤ min 1 (gfPiecePiece d idx g s y y') :=
          le_min zero_le_one (gfPiecePiece_nonneg hd hp y y')
        have := hle1 y y''
        linarith
      rw [he, he']
      obtain ⟨m, n, hm⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s) y y'
      obtain ⟨n', m'', hm'⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s)
        y' y''
      rw [hm, hm']
      by_cases h3 : idx y = idx y''
      · rw [glueFamily_restrict_piece h3]
        have hgg : ∀ k : L, g (idx y'') k = g (idx y) k := fun k => by rw [h3]
        have hr : r y y'' ≤ s y m + s y'' m := hp.tri_ssr y y'' m h3
        have hs : s y'' m ≤ s y'' m'' + d (g (idx y) m'') (g (idx y) m) := by
          have := hp.tri_ssd y'' m m''
          rwa [hgg, hgg] at this
        have hchain1 : d (g (idx y) m'') (g (idx y) m) ≤
            d (g (idx y) m'') (g (idx y') n') +
              d (g (idx y') n') (g (idx y) m) := hd.triangle _ _ _
        have hchain2 : d (g (idx y') n') (g (idx y) m) ≤
            d (g (idx y') n') (g (idx y') n) + d (g (idx y') n) (g (idx y) m) :=
          hd.triangle _ _ _
        have hmid := hp.tri_dss y' n' n
        have e1 : d (g (idx y) m'') (g (idx y') n') = d (g (idx y') n') (g (idx y) m'') :=
          hd.symm _ _
        have e2 : d (g (idx y') n) (g (idx y) m) = d (g (idx y) m) (g (idx y') n) :=
          hd.symm _ _
        rw [hgg m'']
        linarith
      · rw [glueFamily_inr_inr, if_neg h3]
        have hle := gfPiecePiece_le (d := d) (idx := idx) (g := g) (s := s) y y'' m m''
        have hchain1 : d (g (idx y) m) (g (idx y'') m'') ≤
            d (g (idx y) m) (g (idx y') n) + d (g (idx y') n) (g (idx y'') m'') :=
          hd.triangle _ _ _
        have hchain2 : d (g (idx y') n) (g (idx y'') m'') ≤
            d (g (idx y') n) (g (idx y') n') + d (g (idx y') n') (g (idx y'') m'') :=
          hd.triangle _ _ _
        have hmid := hp.tri_dss y' n n'
        have hmin := min_le_right 1 (gfPiecePiece d idx g s y y'')
        linarith

/-- **Tier 4b.** The amalgam of a family of pieces glued to a common base along finite loci
is a bounded-by-one pseudometric. -/
theorem glueFamily_isBddPseudo : IsBddPseudo (glueFamily d idx g r s) := by
  have hnn : ∀ a b : X ⊕ Y, 0 ≤ glueFamily d idx g r s a b := by
    rintro (x | y) (x' | y')
    · exact hd.nonneg _ _
    · exact le_min zero_le_one (gfBasePiece_nonneg hd hp _ _)
    · exact le_min zero_le_one (gfBasePiece_nonneg hd hp _ _)
    · rw [glueFamily_inr_inr]
      split
      · exact hp.r_nonneg _ _
      · exact le_min zero_le_one (gfPiecePiece_nonneg hd hp _ _)
  have hone : ∀ a b : X ⊕ Y, glueFamily d idx g r s a b ≤ 1 := by
    rintro (x | y) (x' | y')
    · exact hd.le_one _ _
    · exact min_le_left _ _
    · exact min_le_left _ _
    · rw [glueFamily_inr_inr]
      split
      · exact hp.r_le_one _ _
      · exact min_le_left _ _
  have hsymm : ∀ a b : X ⊕ Y, glueFamily d idx g r s a b = glueFamily d idx g r s b a := by
    rintro (x | y) (x' | y')
    · exact hd.symm _ _
    · rfl
    · rfl
    · rw [glueFamily_inr_inr, glueFamily_inr_inr]
      by_cases h : idx y = idx y'
      · rw [if_pos h, if_pos h.symm, hp.r_symm]
      · rw [if_neg h, if_neg (Ne.symm h), gfPiecePiece_symm hd]
  refine ⟨hnn, hone, ?_, hsymm, ?_⟩
  · rintro (x | y)
    · exact hd.diag _
    · rw [glueFamily_inr_inr, if_pos rfl, hp.r_diag]
  · rintro (x | y) (x' | y') (x'' | y'')
    · exact hd.triangle _ _ _
    · exact gf_tri_BBP hd _ _ _
    · exact gf_tri_BPB hd hp _ _ _
    · exact gf_tri_BPP hd hp _ _ _
    · -- (piece, base, base)
      have h : min 1 (gfBasePiece d idx g s x'' y) ≤
          d x'' x' + min 1 (gfBasePiece d idx g s x' y) := gf_tri_BBP hd x'' x' y
      have e := hd.symm x'' x'
      show min 1 (gfBasePiece d idx g s x'' y) ≤ min 1 (gfBasePiece d idx g s x' y) + d x' x''
      linarith
    · -- (piece, base, piece)
      exact gf_tri_PBP hd hp _ _ _
    · -- (piece, piece, base)
      have h := gf_tri_BPP hd hp x'' y' y
      have hs := hsymm (Sum.inr y') (Sum.inr y)
      show min 1 (gfBasePiece d idx g s x'' y) ≤
        glueFamily d idx g r s (Sum.inr y) (Sum.inr y') +
          min 1 (gfBasePiece d idx g s x'' y')
      linarith
    · exact gf_tri_PPP hd hp _ _ _

/-- **Tier 4b, the base–piece dichotomy.** Every distance from the base to a new point is
either at the ceiling `1`, or is realized by a geodesic through the locus of the piece. -/
theorem glueFamily_dichotomy_base_piece (x : X) (y : Y) :
    glueFamily d idx g r s (Sum.inl x) (Sum.inr y) = 1 ∨
      ∃ l : L, glueFamily d idx g r s (Sum.inl x) (Sum.inr y) =
        glueFamily d idx g r s (Sum.inl x) (Sum.inl (g (idx y) l)) +
          glueFamily d idx g r s (Sum.inl (g (idx y) l)) (Sum.inr y) := by
  obtain ⟨l, hl⟩ := gfBasePiece_exists (d := d) (idx := idx) (g := g) (s := s) x y
  rcases min_cases 1 (gfBasePiece d idx g s x y) with ⟨he, -⟩ | ⟨he, -⟩
  · exact Or.inl (by rw [glueFamily_inl_inr, he])
  · refine Or.inr ⟨l, ?_⟩
    rw [glueFamily_inl_inr, he, hl, glueFamily_restrict_locus hd hp y l,
      glueFamily_restrict_base]

/-- **Tier 4b, the piece–piece dichotomy.** Every distance between new points of two
different pieces is either at the ceiling `1`, or is realized by a geodesic through the two
loci, giving a tight three-link chain. -/
theorem glueFamily_dichotomy_piece_piece {y y' : Y} (hij : idx y ≠ idx y') :
    glueFamily d idx g r s (Sum.inr y) (Sum.inr y') = 1 ∨
      ∃ l l' : L, glueFamily d idx g r s (Sum.inr y) (Sum.inr y') =
        glueFamily d idx g r s (Sum.inr y) (Sum.inl (g (idx y) l)) +
          glueFamily d idx g r s (Sum.inl (g (idx y) l)) (Sum.inl (g (idx y') l')) +
            glueFamily d idx g r s (Sum.inl (g (idx y') l')) (Sum.inr y') := by
  obtain ⟨l, l', hl⟩ := gfPiecePiece_exists (d := d) (idx := idx) (g := g) (s := s) y y'
  rw [glueFamily_inr_inr, if_neg hij]
  rcases min_cases 1 (gfPiecePiece d idx g s y y') with ⟨he, -⟩ | ⟨he, -⟩
  · exact Or.inl he
  · refine Or.inr ⟨l, l', ?_⟩
    have e1 : glueFamily d idx g r s (Sum.inr y) (Sum.inl (g (idx y) l)) = s y l := by
      rw [← glueFamily_restrict_locus hd hp y l]
      exact (glueFamily_isBddPseudo hd hp).symm _ _
    have e2 : glueFamily d idx g r s (Sum.inl (g (idx y') l')) (Sum.inr y') = s y' l' :=
      glueFamily_restrict_locus hd hp y' l'
    rw [he, hl, e1, e2, glueFamily_restrict_base]

end Triangle
