import Mathlib

/-!
# Perturbations of bounded-by-one pseudometrics

Formalization of §2 of *Every Separable Metric Space Extends to an Extreme One*
(Feldman–Kehoe).

A "metric" here means a bounded-by-`1` pseudometric on a bare type `X`, carried as *data*
`d : X → X → ℝ` together with the predicate `IsBddPseudo d`, since the whole subject is the
convex set of such data.
-/

set_option autoImplicit false

open scoped BigOperators

variable {X : Type*}

/-- `d` is a bounded-by-one pseudometric on `X`. -/
structure IsBddPseudo (d : X → X → ℝ) : Prop where
  nonneg   : ∀ x y, 0 ≤ d x y
  le_one   : ∀ x y, d x y ≤ 1
  diag     : ∀ x, d x x = 0
  symm     : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The set of bounded-by-one pseudometrics on `X`, the paper's `M̄(X)`. -/
def bddPseudoSet (X : Type*) : Set (X → X → ℝ) := {d | IsBddPseudo d}

/-- `ε` is a perturbation of `d`: symmetric, vanishing on the diagonal, and with both
`d + ε` and `d - ε` bounded-by-one pseudometrics. -/
def IsPerturbation (d ε : X → X → ℝ) : Prop :=
  (∀ x y, ε x y = ε y x) ∧ (∀ x, ε x x = 0) ∧
  IsBddPseudo (fun x y => d x y + ε x y) ∧
  IsBddPseudo (fun x y => d x y - ε x y)

/-- The paper's working notion of extremality: no nonzero perturbation. -/
def Rigid (d : X → X → ℝ) : Prop :=
  ∀ ε, IsPerturbation d ε → ∀ x y, ε x y = 0

namespace IsBddPseudo

/-- For a bounded-by-one pseudometric, `|d x y - d z w| ≤ d x z + d y w`. -/
theorem abs_sub_le_add {d : X → X → ℝ} (hd : IsBddPseudo d) (x y z w : X) :
    |d x y - d z w| ≤ d x z + d y w := by
  have h1 : d x y ≤ d x z + d z w + d w y := by
    have := hd.triangle x z y
    have := hd.triangle z w y
    linarith
  have h2 : d z w ≤ d z x + d x y + d y w := by
    have := hd.triangle z x w
    have := hd.triangle x y w
    linarith
  have e1 : d w y = d y w := hd.symm w y
  have e2 : d z x = d x z := hd.symm z x
  rw [abs_le]
  constructor <;> linarith

end IsBddPseudo

/-- The set of bounded-by-one pseudometrics on `X` is convex (paper §1). -/
theorem convex_bddPseudo : Convex ℝ (bddPseudoSet X) := by
  rintro a ha b hb s t hs ht hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have := ha.nonneg x y
    have := hb.nonneg x y
    have h1 : 0 ≤ s * a x y := mul_nonneg hs (ha.nonneg x y)
    have h2 : 0 ≤ t * b x y := mul_nonneg ht (hb.nonneg x y)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using add_nonneg h1 h2
  · intro x y
    have h1 : s * a x y ≤ s * 1 := by
      exact mul_le_mul_of_nonneg_left (ha.le_one x y) hs
    have h2 : t * b x y ≤ t * 1 := by
      exact mul_le_mul_of_nonneg_left (hb.le_one x y) ht
    have : s * a x y + t * b x y ≤ 1 := by nlinarith
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  · intro x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha.diag x, hb.diag x]
  · intro x y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha.symm x y, hb.symm x y]
  · intro x y z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : s * a x z ≤ s * (a x y + a y z) :=
      mul_le_mul_of_nonneg_left (ha.triangle x y z) hs
    have h2 : t * b x z ≤ t * (b x y + b y z) :=
      mul_le_mul_of_nonneg_left (hb.triangle x y z) ht
    nlinarith

/-- Paper Proposition 2.2: rigidity is exactly extremality in `M̄(X)`. -/
theorem rigid_iff_extremePoint (d : X → X → ℝ) (hd : IsBddPseudo d) :
    Rigid d ↔ d ∈ (bddPseudoSet X).extremePoints ℝ := by
  constructor
  · intro hrig
    refine ⟨hd, ?_⟩
    rintro a ha b hb ⟨s, t, hs, ht, hst, hab⟩
    set m : ℝ := min s t with hm
    have hmpos : 0 < m := lt_min hs ht
    have hms : m ≤ s := min_le_left _ _
    have hmt : m ≤ t := min_le_right _ _
    set e : X → X → ℝ := fun x y => m * (a x y - b x y) with he
    have hdplus : (fun x y => d x y + e x y) = (s + m) • a + (t - m) • b := by
      funext x y
      have : d x y = s * a x y + t * b x y := by
        have := congrFun (congrFun hab x) y
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this.symm
      simp only [he, this, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdminus : (fun x y => d x y - e x y) = (s - m) • a + (t + m) • b := by
      funext x y
      have : d x y = s * a x y + t * b x y := by
        have := congrFun (congrFun hab x) y
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this.symm
      simp only [he, this, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hpert : IsPerturbation d e := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y; simp only [he, ha.symm x y, hb.symm x y]
      · intro x; simp [he, ha.diag x, hb.diag x]
      · rw [hdplus]
        exact convex_bddPseudo ha hb (by linarith) (by linarith) (by linarith)
      · rw [hdminus]
        exact convex_bddPseudo ha hb (by linarith) (by linarith) (by linarith)
    have hzero := hrig e hpert
    have hab' : a = b := by
      funext x y
      have := hzero x y
      simp only [he] at this
      have := mul_eq_zero.mp this
      rcases this with h | h
      · exact absurd h (ne_of_gt hmpos)
      · linarith
    subst hab'
    funext x y
    have := congrFun (congrFun hab x) y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have : (s + t) * a x y = d x y := by linarith [this]
    rw [hst, one_mul] at this
    exact this
  · rintro ⟨-, hext⟩ e hpert x y
    obtain ⟨hsymm, hdiag, hplus, hminus⟩ := hpert
    have hmem : d ∈ openSegment ℝ (fun x y => d x y + e x y) (fun x y => d x y - e x y) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext u v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := hext hplus hminus hmem
    have := congrFun (congrFun this x) y
    simpa using this

/-! ### Tier 2: the perturbation lemmas -/

/-- Paper Lemma 2.3: `|ε x y| ≤ min (d x y) (1 - d x y)`. -/
theorem abs_pert_le (d ε : X → X → ℝ) (h : IsPerturbation d ε) (x y : X) :
    |ε x y| ≤ min (d x y) (1 - d x y) := by
  obtain ⟨-, -, hplus, hminus⟩ := h
  have h1 : 0 ≤ d x y + ε x y := hplus.nonneg x y
  have h2 : 0 ≤ d x y - ε x y := hminus.nonneg x y
  have h3 : d x y + ε x y ≤ 1 := hplus.le_one x y
  have h4 : d x y - ε x y ≤ 1 := hminus.le_one x y
  refine le_min ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith

theorem pert_eq_zero_of_dist_eq_zero {d ε : X → X → ℝ} (h : IsPerturbation d ε) {x y : X}
    (hxy : d x y = 0) : ε x y = 0 := by
  have := abs_pert_le d ε h x y
  rw [hxy] at this
  have : |ε x y| ≤ 0 := le_trans this (min_le_left _ _)
  simpa using abs_nonpos_iff.mp this

theorem pert_eq_zero_of_dist_eq_one {d ε : X → X → ℝ} (h : IsPerturbation d ε) {x y : X}
    (hxy : d x y = 1) : ε x y = 0 := by
  have := abs_pert_le d ε h x y
  rw [hxy] at this
  have : |ε x y| ≤ 0 := by
    refine le_trans this ?_
    simp
  simpa using abs_nonpos_iff.mp this

/-- Paper Lemma 2.4: tight triangles are preserved by perturbations. -/
theorem pert_add_of_tight (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {x y z : X} (htight : d x z = d x y + d y z) :
    ε x z = ε x y + ε y z := by
  obtain ⟨-, -, hplus, hminus⟩ := h
  have h1 := hplus.triangle x y z
  have h2 := hminus.triangle x y z
  simp only at h1 h2
  linarith

/-- Paper Corollary 2.6: restriction of a perturbation to a subset. -/
theorem isPerturbation_restrict (d ε : X → X → ℝ) (h : IsPerturbation d ε) (A : Set X) :
    IsPerturbation (fun a b : A => d a b) (fun a b : A => ε a b) := by
  obtain ⟨hsymm, hdiag, hplus, hminus⟩ := h
  refine ⟨fun a b => hsymm a b, fun a => hdiag a, ?_, ?_⟩
  · exact ⟨fun a b => hplus.nonneg a b, fun a b => hplus.le_one a b,
      fun a => hplus.diag a, fun a b => hplus.symm a b, fun a b c => hplus.triangle a b c⟩
  · exact ⟨fun a b => hminus.nonneg a b, fun a b => hminus.le_one a b,
      fun a => hminus.diag a, fun a b => hminus.symm a b, fun a b c => hminus.triangle a b c⟩

theorem pert_eq_zero_on_of_rigid_restrict (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {A : Set X} (hA : Rigid (fun a b : A => d a b)) :
    ∀ a ∈ A, ∀ b ∈ A, ε a b = 0 := by
  intro a ha b hb
  exact hA _ (isPerturbation_restrict d ε h A) ⟨a, ha⟩ ⟨b, hb⟩

/-! ### Tier 2 §3.4: density -/

/-- Density with respect to the pseudometric `d`, phrased without a topology instance. -/
def DenseFor (d : X → X → ℝ) (A : Set X) : Prop :=
  ∀ x : X, ∀ η > 0, ∃ a ∈ A, d x a < η

/-- Paper Lemma 2.5: a perturbation vanishing on a `d`-dense set vanishes everywhere. -/
theorem pert_eq_zero_of_dense (d ε : X → X → ℝ) (h : IsPerturbation d ε)
    {A : Set X} (hA : DenseFor d A) (hzero : ∀ a ∈ A, ∀ b ∈ A, ε a b = 0) :
    ∀ x y, ε x y = 0 := by
  have hd : IsBddPseudo d := by
    obtain ⟨-, -, hplus, hminus⟩ := h
    refine ⟨fun x y => by have := hplus.nonneg x y; have := hminus.nonneg x y; simp only at *; linarith,
      fun x y => by have := hplus.le_one x y; have := hminus.le_one x y; simp only at *; linarith,
      fun x => by have := hplus.diag x; have := hminus.diag x; simp only at *; linarith,
      fun x y => by
        have h1 := hplus.symm x y; have h2 := hminus.symm x y; simp only at h1 h2; linarith,
      fun x y z => by
        have h1 := hplus.triangle x y z; have h2 := hminus.triangle x y z
        simp only at h1 h2; linarith⟩
  intro x y
  obtain ⟨hsymm, hdiag, hplus, hminus⟩ := h
  have hpert : IsPerturbation d ε := ⟨hsymm, hdiag, hplus, hminus⟩
  set r : X → X → ℝ := fun u v => d u v + ε u v with hr
  have hrho : IsBddPseudo r := hplus
  -- key estimate
  have key : ∀ η > 0, |ε x y| ≤ η := by
    intro η hη
    obtain ⟨a, haA, hxa⟩ := hA x (η / 8) (by linarith)
    obtain ⟨b, hbA, hyb⟩ := hA y (η / 8) (by linarith)
    have hεxa : |ε x a| ≤ d x a := le_trans (abs_pert_le d ε hpert x a) (min_le_left _ _)
    have hεyb : |ε y b| ≤ d y b := le_trans (abs_pert_le d ε hpert y b) (min_le_left _ _)
    have hrxa : r x a ≤ 2 * d x a := by
      have := abs_le.mp hεxa
      simp only [hr]; linarith [this.1, this.2]
    have hryb : r y b ≤ 2 * d y b := by
      have := abs_le.mp hεyb
      simp only [hr]; linarith [this.1, this.2]
    have h1 : |r x y - r a b| ≤ r x a + r y b := hrho.abs_sub_le_add x y a b
    have h2 : |d x y - d a b| ≤ d x a + d y b := hd.abs_sub_le_add x y a b
    have h3 : r a b = d a b := by
      simp only [hr, hzero a haA b hbA, add_zero]
    have h4 : ε x y = (r x y - r a b) + (d a b - d x y) := by
      rw [h3]; simp only [hr]; ring
    have hxa0 : 0 ≤ d x a := hd.nonneg x a
    have hyb0 : 0 ≤ d y b := hd.nonneg y b
    calc |ε x y| ≤ |r x y - r a b| + |d a b - d x y| := by rw [h4]; exact abs_add_le _ _
      _ ≤ (r x a + r y b) + (d x a + d y b) := by
          have : |d a b - d x y| = |d x y - d a b| := abs_sub_comm _ _
          rw [this]; linarith
      _ ≤ 4 * (d x a + d y b) := by linarith
      _ ≤ η := by linarith
  have : |ε x y| ≤ 0 := by
    by_contra hc
    push_neg at hc
    have := key (|ε x y| / 2) (by linarith)
    linarith
  simpa using abs_nonpos_iff.mp this
