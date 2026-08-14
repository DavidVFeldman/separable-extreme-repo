import RequestProject.Perturbation

/-!
# Tier 5: Proposition 5.1, discharged

Every rational `q ∈ (0,1]` occurs as a distance in a finite *rigid* bounded-by-one
pseudometric.  This is the paper's Proposition 5.1, which Tiers 1–4 carried as the
hypothesis `hrat`.

The witness is a single family of *bowtie* metrics, `B_b := B_{1,2,2,…,2}`: one point at
level `0` and two points at each of the levels `1,…,b`, at raw distance `|i - j|` between
levels `i ≠ j` and `2` between two distinct points of the same level, all divided by `b`.
Its values on distinct points are exactly `1/b, 2/b, …, b/b`, so it realizes every rational
`a/b ∈ (0,1]`; writing `q = (2·num)/(2·den)` puts every `q ∈ (0,1]` (including `q = 1`) in
that shape with `b ≥ 2`, so no separate two-point case is needed.  This single family
supersedes the two-case argument (`q = 1`, and `q = a/b` with `0 < a < b`) of the paper's
proof sketch.

Rigidity is proved directly in the perturbation vocabulary of `Perturbation.lean`: the tight
triples of the bowtie are exactly the *chains* (three strictly increasing levels) and the
*vees* (two distinct points of one level seen from a point of an adjacent level), and those
relations alone force any perturbation to be `λ` times the raw metric, whence `0` because
the extreme levels are at distance exactly `1`.
-/

set_option autoImplicit false

namespace Bowtie

/-- The carrier of the bowtie `B_b`: one point at level `0`, and two points at each of the
levels `1, …, b`. -/
abbrev Bw (b : ℕ) : Type := Unit ⊕ (Fin b × Bool)

variable {b : ℕ}

/-- The apex of the bowtie: the unique point at level `0`. -/
def apex (b : ℕ) : Bw b := Sum.inl ()

/-- The two points at level `j + 1`. -/
def pt (j : Fin b) (s : Bool) : Bw b := Sum.inr (j, s)

/-- The level of a point of the bowtie. -/
def lvl : Bw b → ℕ
  | Sum.inl _ => 0
  | Sum.inr (i, _) => (i : ℕ) + 1

@[simp] theorem lvl_apex : lvl (apex b) = 0 := rfl

@[simp] theorem lvl_pt (j : Fin b) (s : Bool) : lvl (pt j s) = (j : ℕ) + 1 := rfl

theorem lvl_le (x : Bw b) : lvl x ≤ b := by
  cases x with
  | inl _ => simp [lvl]
  | inr p => exact p.1.2

theorem eq_apex_of_lvl_zero {x : Bw b} (h : lvl x = 0) : x = apex b := by
  cases x with
  | inl u => cases u; rfl
  | inr p => simp [lvl] at h

theorem exists_pt_of_le {m : ℕ} (hm : m ≤ b) : ∃ x : Bw b, lvl x = m := by
  cases m with
  | zero => exact ⟨apex b, rfl⟩
  | succ n =>
      have hn : n < b := by omega
      exact ⟨pt ⟨n, hn⟩ false, rfl⟩

theorem pt_ne {j : Fin b} : pt j false ≠ pt j true := by
  simp [pt]

/-- The unscaled bowtie distance. -/
def raw (b : ℕ) (x y : Bw b) : ℝ :=
  if x = y then 0 else if lvl x = lvl y then 2 else |(lvl x : ℝ) - (lvl y : ℝ)|

/-- The bowtie metric `B_b`, normalized so that its maximum value is `1`. -/
noncomputable def bowtie (b : ℕ) (x y : Bw b) : ℝ := raw b x y / b

@[simp] theorem raw_self (x : Bw b) : raw b x x = 0 := by simp [raw]

theorem raw_of_lvl_ne {x y : Bw b} (h : lvl x ≠ lvl y) :
    raw b x y = |(lvl x : ℝ) - (lvl y : ℝ)| := by
  have hxy : x ≠ y := by rintro rfl; exact h rfl
  simp [raw, hxy, h]

theorem raw_of_lvl_eq {x y : Bw b} (h : lvl x = lvl y) (hne : x ≠ y) : raw b x y = 2 := by
  simp [raw, hne, h]

theorem raw_nonneg (x y : Bw b) : 0 ≤ raw b x y := by
  by_cases h : lvl x = lvl y
  · by_cases hxy : x = y
    · simp [hxy]
    · rw [raw_of_lvl_eq h hxy]; norm_num
  · rw [raw_of_lvl_ne h]; exact abs_nonneg _

theorem raw_comm (x y : Bw b) : raw b x y = raw b y x := by
  by_cases h : lvl x = lvl y
  · by_cases hxy : x = y
    · simp [hxy]
    · rw [raw_of_lvl_eq h hxy, raw_of_lvl_eq h.symm (Ne.symm hxy)]
  · rw [raw_of_lvl_ne h, raw_of_lvl_ne (Ne.symm h), abs_sub_comm]

theorem abs_lvl_sub_le_raw (x y : Bw b) :
    |(lvl x : ℝ) - (lvl y : ℝ)| ≤ raw b x y := by
  by_cases h : lvl x = lvl y
  · have : (lvl x : ℝ) = (lvl y : ℝ) := by exact_mod_cast h
    rw [this]
    simpa using raw_nonneg x y
  · rw [raw_of_lvl_ne h]

theorem one_le_abs_lvl_sub {x y : Bw b} (h : lvl x ≠ lvl y) :
    (1 : ℝ) ≤ |(lvl x : ℝ) - (lvl y : ℝ)| := by
  rcases Nat.lt_or_ge (lvl x) (lvl y) with hlt | hge
  · rw [abs_of_nonpos (by
      have : (lvl x : ℝ) ≤ (lvl y : ℝ) := by exact_mod_cast hlt.le
      linarith)]
    have : (lvl x : ℝ) + 1 ≤ (lvl y : ℝ) := by exact_mod_cast hlt
    linarith
  · have hlt : lvl y < lvl x := lt_of_le_of_ne hge (Ne.symm h)
    rw [abs_of_nonneg (by
      have : (lvl y : ℝ) ≤ (lvl x : ℝ) := by exact_mod_cast hge
      linarith)]
    have : (lvl y : ℝ) + 1 ≤ (lvl x : ℝ) := by exact_mod_cast hlt
    linarith

theorem raw_le_b (hb : 2 ≤ b) (x y : Bw b) : raw b x y ≤ b := by
  by_cases h : lvl x = lvl y
  · by_cases hxy : x = y
    · simp only [hxy, raw_self]
      positivity
    · rw [raw_of_lvl_eq h hxy]
      exact_mod_cast hb
  · rw [raw_of_lvl_ne h]
    have h1 : (lvl x : ℝ) ≤ b := by exact_mod_cast lvl_le x
    have h2 : (lvl y : ℝ) ≤ b := by exact_mod_cast lvl_le y
    have h3 : (0 : ℝ) ≤ lvl x := by positivity
    have h4 : (0 : ℝ) ≤ lvl y := by positivity
    rw [abs_le]
    constructor <;> linarith

theorem raw_triangle (x y z : Bw b) : raw b x z ≤ raw b x y + raw b y z := by
  by_cases hxz : lvl x = lvl z
  · by_cases hxzp : x = z
    · simp only [hxzp, raw_self]
      have := raw_nonneg z y
      have := raw_nonneg y z
      linarith
    · rw [raw_of_lvl_eq hxz hxzp]
      by_cases hy : lvl y = lvl x
      · -- `y` sits at the same level: it differs from `x` or from `z`
        have hyz : lvl y = lvl z := hy.trans hxz
        by_cases hyx : y = x
        · have hyz' : y ≠ z := by rw [hyx]; exact hxzp
          rw [raw_of_lvl_eq hyz hyz']
          have := raw_nonneg x y
          linarith
        · rw [raw_of_lvl_eq hy.symm (Ne.symm hyx)]
          have := raw_nonneg y z
          linarith
      · have h1 : (1 : ℝ) ≤ raw b x y := by
          refine le_trans (one_le_abs_lvl_sub (Ne.symm hy)) (abs_lvl_sub_le_raw x y)
        have h2 : (1 : ℝ) ≤ raw b y z := by
          refine le_trans (one_le_abs_lvl_sub ?_) (abs_lvl_sub_le_raw y z)
          rw [← hxz]; exact hy
        linarith
  · rw [raw_of_lvl_ne hxz]
    have h1 := abs_lvl_sub_le_raw (b := b) x y
    have h2 := abs_lvl_sub_le_raw (b := b) y z
    have h3 : |(lvl x : ℝ) - (lvl z : ℝ)|
        ≤ |(lvl x : ℝ) - (lvl y : ℝ)| + |(lvl y : ℝ) - (lvl z : ℝ)| := by
      exact abs_sub_le _ _ _
    linarith

/-- The bowtie metric is a bounded-by-one pseudometric, for `b ≥ 2`. -/
theorem bowtie_isBddPseudo (hb : 2 ≤ b) : IsBddPseudo (bowtie b) := by
  have hbpos : (0 : ℝ) < b := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact div_nonneg (raw_nonneg x y) hbpos.le
  · intro x y
    rw [bowtie, div_le_one hbpos]
    exact raw_le_b hb x y
  · intro x; simp [bowtie]
  · intro x y; simp [bowtie, raw_comm x y]
  · intro x y z
    rw [bowtie, bowtie, bowtie, ← add_div]
    exact (div_le_div_iff_of_pos_right hbpos).mpr (raw_triangle x y z)

/-! ### The tight triples -/

/-- A *chain*: three strictly increasing levels form a tight triple. -/
theorem bowtie_chain {x y z : Bw b} (h1 : lvl x < lvl y) (h2 : lvl y < lvl z) :
    bowtie b x z = bowtie b x y + bowtie b y z := by
  have e1 : raw b x z = |(lvl x : ℝ) - (lvl z : ℝ)| :=
    raw_of_lvl_ne (by omega)
  have e2 : raw b x y = |(lvl x : ℝ) - (lvl y : ℝ)| :=
    raw_of_lvl_ne (by omega)
  have e3 : raw b y z = |(lvl y : ℝ) - (lvl z : ℝ)| :=
    raw_of_lvl_ne (by omega)
  have c1 : (lvl x : ℝ) ≤ lvl y := by exact_mod_cast h1.le
  have c2 : (lvl y : ℝ) ≤ lvl z := by exact_mod_cast h2.le
  rw [bowtie, bowtie, bowtie, e1, e2, e3, ← add_div,
    abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring_nf

/-- A *vee*: two distinct points of one level, seen from a point of an adjacent level,
form a tight triple. -/
theorem bowtie_vee {x y w : Bw b} (hlvl : lvl x = lvl y) (hne : x ≠ y)
    (hw : lvl w + 1 = lvl x ∨ lvl x + 1 = lvl w) :
    bowtie b x y = bowtie b x w + bowtie b w y := by
  have hwx : lvl w ≠ lvl x := by omega
  have hwy : lvl w ≠ lvl y := by omega
  have e1 : raw b x y = 2 := raw_of_lvl_eq hlvl hne
  have e2 : raw b x w = |(lvl x : ℝ) - (lvl w : ℝ)| := raw_of_lvl_ne (Ne.symm hwx)
  have e3 : raw b w y = |(lvl w : ℝ) - (lvl y : ℝ)| := raw_of_lvl_ne hwy
  have e4 : |(lvl x : ℝ) - (lvl w : ℝ)| = 1 := by
    rcases hw with h | h
    · have : (lvl w : ℝ) + 1 = lvl x := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (lvl x : ℝ) + 1 = lvl w := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
  have e5 : |(lvl w : ℝ) - (lvl y : ℝ)| = 1 := by
    have hl : (lvl x : ℝ) = lvl y := by exact_mod_cast hlvl
    rw [abs_sub_comm, ← hl, e4]
  rw [bowtie, bowtie, bowtie, e1, e2, e3, e4, e5, ← add_div]
  norm_num

/-! ### Rigidity -/

section Rigid

variable (hb : 2 ≤ b) {ε : Bw b → Bw b → ℝ}

/-- The value of a perturbation against the apex. -/
private def fval (ε : Bw b → Bw b → ℝ) (u : Bw b) : ℝ := ε (apex b) u

omit hb in
/-- Across levels, a perturbation is determined by its values against the apex. -/
theorem pert_cross (hε : IsPerturbation (bowtie b) ε) {u v : Bw b} (h : lvl u < lvl v) :
    ε u v = fval ε v - fval ε u := by
  by_cases h0 : lvl u = 0
  · have hu : u = apex b := eq_apex_of_lvl_zero h0
    subst hu
    have h0' : fval ε (apex b) = 0 := hε.2.1 _
    simp only [fval] at h0' ⊢
    linarith
  · have h1 : lvl (apex b) < lvl u := by rw [lvl_apex]; omega
    have := pert_add_of_tight (bowtie b) ε hε (bowtie_chain h1 h)
    simp only [fval]
    linarith

omit hb in
/-- The vee relation, downwards. -/
theorem pert_vee_down (hε : IsPerturbation (bowtie b) ε) {u v w : Bw b}
    (hlvl : lvl u = lvl v) (hne : u ≠ v) (hw : lvl w + 1 = lvl u) :
    ε u v = (fval ε u - fval ε w) + (fval ε v - fval ε w) := by
  have ht := pert_add_of_tight (bowtie b) ε hε (bowtie_vee hlvl hne (Or.inl hw))
  have h1 : ε w u = fval ε u - fval ε w := pert_cross hε (by omega)
  have h2 : ε w v = fval ε v - fval ε w := pert_cross hε (by omega)
  have h3 : ε u w = ε w u := hε.1 u w
  rw [ht, h3, h1, h2]

omit hb in
/-- The vee relation, upwards. -/
theorem pert_vee_up (hε : IsPerturbation (bowtie b) ε) {u v w : Bw b}
    (hlvl : lvl u = lvl v) (hne : u ≠ v) (hw : lvl u + 1 = lvl w) :
    ε u v = (fval ε w - fval ε u) + (fval ε w - fval ε v) := by
  have ht := pert_add_of_tight (bowtie b) ε hε (bowtie_vee hlvl hne (Or.inr hw))
  have h1 : ε u w = fval ε w - fval ε u := pert_cross hε (by omega)
  have h2 : ε v w = fval ε w - fval ε v := pert_cross hε (by omega)
  have h3 : ε w v = ε v w := hε.1 w v
  rw [ht, h1, h3, h2]

include hb in
/-- Against the apex, a perturbation vanishes at the top level: those pairs are at
distance exactly `1`. -/
theorem pert_top (hε : IsPerturbation (bowtie b) ε) {u : Bw b} (h : lvl u = b) :
    fval ε u = 0 := by
  have hbpos : (0 : ℝ) < b := by
    have : (0 : ℕ) < b := by omega
    exact_mod_cast this
  have hne : lvl (apex b) ≠ lvl u := by rw [lvl_apex, h]; omega
  have h1 : bowtie b (apex b) u = 1 := by
    rw [bowtie, raw_of_lvl_ne hne, lvl_apex, h, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg hbpos.le, div_self (ne_of_gt hbpos)]
  exact pert_eq_zero_of_dist_eq_one hε h1

include hb in
/-- Two points of the same level have the same value against the apex. -/
theorem pert_pair (hε : IsPerturbation (bowtie b) ε) {u v : Bw b} (h : lvl u = lvl v) :
    fval ε u = fval ε v := by
  rcases eq_or_ne u v with rfl | hne
  · rfl
  rcases eq_or_lt_of_le (lvl_le u) with hb' | hlt
  · rw [pert_top hb hε hb', pert_top hb hε (h ▸ hb')]
  · -- use the pair of points one level up
    have hidx : lvl u < b := hlt
    set z1 : Bw b := pt ⟨lvl u, hidx⟩ false with hz1
    set z2 : Bw b := pt ⟨lvl u, hidx⟩ true with hz2
    have hz12 : z1 ≠ z2 := pt_ne
    have hl1 : lvl z1 = lvl u + 1 := rfl
    have hl2 : lvl z2 = lvl u + 1 := rfl
    have e1 := pert_vee_down hε (u := z1) (v := z2) (w := u) (by rw [hl1, hl2]) hz12
      (by omega)
    have e2 := pert_vee_down hε (u := z1) (v := z2) (w := v) (by rw [hl1, hl2]) hz12
      (by omega)
    linarith [e1, e2]

/-- The common value of a perturbation against the apex at level `1`. -/
private noncomputable def slope (ε : Bw b → Bw b → ℝ) : ℝ :=
  if h : 0 < b then fval ε (pt ⟨0, h⟩ false) else 0

include hb in
/-- A perturbation is linear in the level: `ε (apex) u = lvl u * λ`. -/
theorem pert_linear (hε : IsPerturbation (bowtie b) ε) :
    ∀ n : ℕ, ∀ u : Bw b, lvl u = n → fval ε u = n * slope ε := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        intro u hu
        rw [eq_apex_of_lvl_zero hu]
        have : fval ε (apex b) = 0 := hε.2.1 _
        simpa using this
    | 1 =>
        intro u hu
        have hb0 : 0 < b := by omega
        have : fval ε u = fval ε (pt (⟨0, hb0⟩ : Fin b) false) :=
          pert_pair hb hε (by rw [hu]; rfl)
        rw [this, slope, dif_pos hb0]
        norm_num
    | (m + 2) =>
        intro u hu
        have hub : m + 2 ≤ b := hu ▸ lvl_le u
        have hmb : m < b := by omega
        set z1 : Bw b := pt ⟨m, hmb⟩ false with hz1
        set z2 : Bw b := pt ⟨m, hmb⟩ true with hz2
        have hl1 : lvl z1 = m + 1 := rfl
        have hl2 : lvl z2 = m + 1 := rfl
        have hz12 : z1 ≠ z2 := pt_ne
        obtain ⟨w, hw⟩ := exists_pt_of_le (b := b) (m := m) (by omega)
        have f1 : fval ε z1 = (m + 1 : ℕ) * slope ε := ih (m + 1) (by omega) z1 hl1
        have f2 : fval ε z2 = (m + 1 : ℕ) * slope ε := ih (m + 1) (by omega) z2 hl2
        have f3 : fval ε w = (m : ℕ) * slope ε := ih m (by omega) w hw
        have e1 := pert_vee_down hε (u := z1) (v := z2) (w := w) (by rw [hl1, hl2]) hz12
          (by omega)
        have e2 := pert_vee_up hε (u := z1) (v := z2) (w := u) (by rw [hl1, hl2]) hz12
          (by omega)
        rw [f1, f2, f3] at e1
        rw [f1, f2] at e2
        push_cast at e1 e2 ⊢
        linarith

include hb in
/-- **Rigidity of the bowtie.** -/
theorem bowtie_rigid : Rigid (bowtie b) := by
  intro ε hε
  -- the slope vanishes, since the apex and the top level are at distance `1`
  obtain ⟨t, ht⟩ := exists_pt_of_le (b := b) (m := b) le_rfl
  have hzero : (b : ℝ) * slope ε = 0 := by
    have := pert_linear hb hε b t ht
    rw [pert_top hb hε ht] at this
    linarith
  have hbne : (b : ℝ) ≠ 0 := by
    have : (0 : ℕ) < b := by omega
    positivity
  have hslope : slope ε = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hbne
    · exact h
  have hf : ∀ u : Bw b, fval ε u = 0 := by
    intro u
    have := pert_linear hb hε (lvl u) u rfl
    rw [hslope] at this
    simpa using this
  intro x y
  rcases lt_trichotomy (lvl x) (lvl y) with h | h | h
  · rw [pert_cross hε h, hf, hf]; ring
  · rcases eq_or_ne x y with rfl | hne
    · exact hε.2.1 x
    · have hx0 : lvl x ≠ 0 := by
        intro h0
        exact hne ((eq_apex_of_lvl_zero h0).trans (eq_apex_of_lvl_zero (h ▸ h0)).symm)
      have hlx := lvl_le x
      obtain ⟨w, hw⟩ := exists_pt_of_le (b := b) (m := lvl x - 1) (by omega)
      rw [pert_vee_down hε (w := w) h hne (by omega), hf, hf, hf]
      ring
  · have := pert_cross hε (u := y) (v := x) h
    rw [hf, hf] at this
    have h2 : ε x y = ε y x := hε.1 x y
    rw [h2, this]
    ring

end Rigid

end Bowtie

/-- **Paper Proposition 5.1.** For every rational `q ∈ (0,1]` there are a finite set `F`, a
rigid (equivalently extreme) bounded-by-one pseudometric `ρ` on `F`, and points `u v : F`
with `ρ u v = q`.

The witness is the bowtie `B_b` of `Bowtie.bowtie` with `b = 2 * q.den`, at the pair
consisting of the apex and a point of level `2 * q.num`. -/
theorem exists_finite_rigid_realizing (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ (F : Type) (_ : Fintype F) (ρ : F → F → ℝ) (u v : F),
      IsBddPseudo ρ ∧ Rigid ρ ∧ ρ u v = (q : ℝ) := by
  classical
  set b : ℕ := 2 * q.den with hbdef
  have hden : 0 < q.den := q.pos
  have hb : 2 ≤ b := by omega
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0
  set a : ℕ := 2 * q.num.toNat with hadef
  have hqdef : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    rw [Rat.cast_def]
  have hdenR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hden
  have hnumR : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hale : a ≤ b := by
    have h1 : (q.num : ℝ) ≤ (q.den : ℝ) := by
      have h2 : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
      rw [hqdef, div_le_one hdenR] at h2
      exact h2
    have h3 : q.num ≤ (q.den : ℤ) := by exact_mod_cast h1
    have h4 : q.num.toNat ≤ q.den := by omega
    omega
  have ha1 : 1 ≤ a := by omega
  have hidx : a - 1 < b := by omega
  refine ⟨Bowtie.Bw b, inferInstance, Bowtie.bowtie b, Bowtie.apex b,
    Bowtie.pt ⟨a - 1, hidx⟩ false, Bowtie.bowtie_isBddPseudo hb, Bowtie.bowtie_rigid hb, ?_⟩
  have hlvl : Bowtie.lvl (Bowtie.pt (⟨a - 1, hidx⟩ : Fin b) false) = a := by
    show (a - 1) + 1 = a
    omega
  have hne : Bowtie.lvl (Bowtie.apex b)
      ≠ Bowtie.lvl (Bowtie.pt (⟨a - 1, hidx⟩ : Fin b) false) := by
    rw [Bowtie.lvl_apex, hlvl]; omega
  have hab : (a : ℝ) / (b : ℝ) = (q : ℝ) := by
    rw [hadef, hbdef, hqdef]
    push_cast
    rw [hnumR]
    field_simp
  rw [Bowtie.bowtie, Bowtie.raw_of_lvl_ne hne, Bowtie.lvl_apex, hlvl, Nat.cast_zero, zero_sub,
    abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a : ℝ))]
  exact hab
