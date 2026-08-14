import RequestProject.Glue

/-!
# The two diagnostic traps

Both statements of §5 of the commission are **false**, and neither is proved here. Instead
each is recorded as a commented-out statement together with an explicit Lean counterexample
that refutes it.

* **Trap A** — gluing without the truncation at `1` (paper Remark 3.2). The untruncated
  amalgam violates `le_one`.
* **Trap B** — the dichotomy for an infinite gluing locus. The infimum need not be attained.
-/

set_option autoImplicit false

/-! ### Two families of examples -/

/-- The discrete `0/1` metric on a type with decidable equality. -/
noncomputable def discreteMetric (T : Type*) [DecidableEq T] : T → T → ℝ :=
  fun a b => if a = b then 0 else 1

theorem discreteMetric_isBddPseudo (T : Type*) [DecidableEq T] :
    IsBddPseudo (discreteMetric T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y; unfold discreteMetric; split <;> norm_num
  · intro x y; unfold discreteMetric; split <;> norm_num
  · intro x; simp [discreteMetric]
  · intro x y; unfold discreteMetric; by_cases h : x = y <;> simp [h, eq_comm]
  · intro x y z
    unfold discreteMetric
    by_cases h1 : x = z
    · simp only [h1]
      positivity
    · by_cases h2 : x = y
      · subst h2
        simp only [if_neg h1]
        split <;> norm_num
      · simp only [if_neg h1, if_neg h2]
        split <;> norm_num

/-- The pullback of the metric of `ℝ` along a map into `[0,1]`. -/
noncomputable def pullbackMetric {T : Type*} (f : T → ℝ) : T → T → ℝ :=
  fun a b => |f a - f b|

theorem pullbackMetric_isBddPseudo {T : Type*} (f : T → ℝ) (h0 : ∀ a, 0 ≤ f a)
    (h1 : ∀ a, f a ≤ 1) : IsBddPseudo (pullbackMetric f) := by
  refine ⟨fun x y => abs_nonneg _, ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [pullbackMetric, abs_le]
    constructor <;> [linarith [h0 x, h1 y]; linarith [h0 y, h1 x]]
  · intro x; simp [pullbackMetric]
  · intro x y; simp [pullbackMetric, abs_sub_comm]
  · intro x y z
    simpa [pullbackMetric] using abs_sub_le (f x) (f y) (f z)

/-! ### Trap A: gluing without the truncation

```lean
-- FALSE. Not provable, and not proved here.
theorem glue_no_truncation_isBddPseudo :
    IsBddPseudo (glueUntruncated d ρ)
```

The untruncated amalgam is not bounded by `1`: with one point on each side and a single
gluing point `z` at distance `1` from both, the cross distance is `2`. The counterexample
below takes `P = F = Q = Unit` and both input metrics discrete, so that both are
bounded-by-one pseudometrics agreeing on `F`, and exhibits a distance of `2`. -/

/-- The cross distance of the amalgam *without* the truncation at `1`. -/
noncomputable def glueCrossUntruncated {P Q F : Type*} [Fintype F] [Nonempty F]
    (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) (x : P) (y : Q) : ℝ :=
  (Finset.univ : Finset F).inf' Finset.univ_nonempty
    (fun z => d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y))

/-- The amalgam without the truncation at `1`. -/
noncomputable def glueUntruncated {P Q F : Type*} [Fintype F] [Nonempty F]
    (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) :
    (P ⊕ F ⊕ Q) → (P ⊕ F ⊕ Q) → ℝ
  | Sum.inl x, Sum.inl x' => d (Sum.inl x) (Sum.inl x')
  | Sum.inl x, Sum.inr (Sum.inl z) => d (Sum.inl x) (Sum.inr z)
  | Sum.inl x, Sum.inr (Sum.inr y) => glueCrossUntruncated d ρ x y
  | Sum.inr (Sum.inl z), Sum.inl x => d (Sum.inr z) (Sum.inl x)
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inl z') => d (Sum.inr z) (Sum.inr z')
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inr y) => ρ (Sum.inl z) (Sum.inr y)
  | Sum.inr (Sum.inr y), Sum.inl x => glueCrossUntruncated d ρ x y
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inl z) => ρ (Sum.inr y) (Sum.inl z)
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inr y') => ρ (Sum.inr y) (Sum.inr y')

/-- Trap A input: the discrete metric on `Unit ⊕ Unit`, used on both sides. -/
noncomputable def trapAmetric : Unit ⊕ Unit → Unit ⊕ Unit → ℝ := discreteMetric _

theorem trapAmetric_isBddPseudo : IsBddPseudo trapAmetric := discreteMetric_isBddPseudo _

/-- The two inputs agree on the gluing locus. -/
theorem trapA_agree : ∀ z z' : Unit,
    trapAmetric (Sum.inr z) (Sum.inr z') = trapAmetric (Sum.inl z) (Sum.inl z') := by
  intro z z'
  simp [trapAmetric, discreteMetric]

/-- The untruncated cross distance of the trap-A example equals `2`. -/
theorem trapA_cross_eq_two :
    glueCrossUntruncated (P := Unit) (Q := Unit) (F := Unit) trapAmetric trapAmetric () () = 2 := by
  simp [glueCrossUntruncated, trapAmetric, discreteMetric]
  norm_num

/-- **Trap A is false.** The untruncated amalgam of two bounded-by-one pseudometrics that
agree on the gluing locus need not be bounded by `1`. -/
theorem glue_no_truncation_not_isBddPseudo :
    ¬ IsBddPseudo (glueUntruncated (P := Unit) (Q := Unit) (F := Unit) trapAmetric trapAmetric) := by
  intro h
  have := h.le_one (Sum.inl ()) (Sum.inr (Sum.inr ()))
  rw [show glueUntruncated (P := Unit) (Q := Unit) (F := Unit) trapAmetric trapAmetric
      (Sum.inl ()) (Sum.inr (Sum.inr ())) = 2 from trapA_cross_eq_two] at this
  norm_num at this

/-! ### Trap B: an infinite gluing locus

```lean
-- FALSE. Not provable, and not proved here.
theorem glue_dichotomy_infinite {F : Type*} [Nonempty F] (x : P) (y : Q) :
    glueIInf d ρ x y = 1 ∨ ∃ z : F, glueIInf d ρ x y = glueIInf d ρ x z + glueIInf d ρ z y
```

With `F = ℕ` the infimum need not be attained. In the counterexample below both inputs are
pullbacks of the metric of `ℝ`: on the left, the `P`-point sits at `0` and `z n` at
`1/2 + 1/(n+2)`; on the right, `z n` sits at `1/(n+2)` and the `Q`-point at `0`. They agree
on the gluing locus, the cross sums are `1/2 + 2/(n+2)`, and the infimum `1/2` is attained
at no `n`. -/

/-- The cross distance of the amalgam with an arbitrary nonempty gluing locus, using `iInf`
in place of the finite minimum. -/
noncomputable def glueCrossIInf {P Q F : Type*} [Nonempty F]
    (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) (x : P) (y : Q) : ℝ :=
  min 1 (⨅ z : F, d (Sum.inl x) (Sum.inr z) + ρ (Sum.inl z) (Sum.inr y))

/-- The amalgam with an arbitrary nonempty gluing locus. -/
noncomputable def glueIInf {P Q F : Type*} [Nonempty F]
    (d : P ⊕ F → P ⊕ F → ℝ) (ρ : F ⊕ Q → F ⊕ Q → ℝ) :
    (P ⊕ F ⊕ Q) → (P ⊕ F ⊕ Q) → ℝ
  | Sum.inl x, Sum.inl x' => d (Sum.inl x) (Sum.inl x')
  | Sum.inl x, Sum.inr (Sum.inl z) => d (Sum.inl x) (Sum.inr z)
  | Sum.inl x, Sum.inr (Sum.inr y) => glueCrossIInf d ρ x y
  | Sum.inr (Sum.inl z), Sum.inl x => d (Sum.inr z) (Sum.inl x)
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inl z') => d (Sum.inr z) (Sum.inr z')
  | Sum.inr (Sum.inl z), Sum.inr (Sum.inr y) => ρ (Sum.inl z) (Sum.inr y)
  | Sum.inr (Sum.inr y), Sum.inl x => glueCrossIInf d ρ x y
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inl z) => ρ (Sum.inr y) (Sum.inl z)
  | Sum.inr (Sum.inr y), Sum.inr (Sum.inr y') => ρ (Sum.inr y) (Sum.inr y')

/-- Positions of the left-hand space of the trap-B example. -/
noncomputable def trapBleftPos : Unit ⊕ ℕ → ℝ
  | Sum.inl _ => 0
  | Sum.inr n => 1 / 2 + 1 / (n + 2)

/-- Positions of the right-hand space of the trap-B example. -/
noncomputable def trapBrightPos : ℕ ⊕ Unit → ℝ
  | Sum.inl n => 1 / (n + 2)
  | Sum.inr _ => 0

noncomputable def trapBleft : Unit ⊕ ℕ → Unit ⊕ ℕ → ℝ := pullbackMetric trapBleftPos
noncomputable def trapBright : ℕ ⊕ Unit → ℕ ⊕ Unit → ℝ := pullbackMetric trapBrightPos

theorem trapB_inv_bounds (n : ℕ) : 0 < 1 / ((n : ℝ) + 2) ∧ 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
  have h : (0:ℝ) < (n : ℝ) + 2 := by positivity
  constructor
  · positivity
  · refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

theorem trapBleft_isBddPseudo : IsBddPseudo trapBleft := by
  refine pullbackMetric_isBddPseudo _ ?_ ?_
  · rintro (x | n)
    · simp [trapBleftPos]
    · have := (trapB_inv_bounds n).1
      simp only [trapBleftPos]
      linarith
  · rintro (x | n)
    · simp [trapBleftPos]
    · have := (trapB_inv_bounds n).2
      simp only [trapBleftPos]
      linarith

theorem trapBright_isBddPseudo : IsBddPseudo trapBright := by
  refine pullbackMetric_isBddPseudo _ ?_ ?_
  · rintro (n | y)
    · have := (trapB_inv_bounds n).1
      simp only [trapBrightPos]
      linarith
    · simp [trapBrightPos]
  · rintro (n | y)
    · have := (trapB_inv_bounds n).2
      simp only [trapBrightPos]
      linarith
    · simp [trapBrightPos]

/-- The two inputs agree on the (infinite) gluing locus. -/
theorem trapB_agree : ∀ m n : ℕ,
    trapBleft (Sum.inr m) (Sum.inr n) = trapBright (Sum.inl m) (Sum.inl n) := by
  intro m n
  simp only [trapBleft, trapBright, pullbackMetric, trapBleftPos, trapBrightPos]
  ring_nf

theorem trapB_sum (n : ℕ) :
    trapBleft (Sum.inl ()) (Sum.inr n) + trapBright (Sum.inl n) (Sum.inr ()) =
      1 / 2 + 2 / ((n : ℝ) + 2) := by
  have h1 := (trapB_inv_bounds n).1
  simp only [trapBleft, trapBright, pullbackMetric, trapBleftPos, trapBrightPos]
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  field_simp
  ring

theorem trapB_iInf :
    (⨅ n : ℕ, trapBleft (Sum.inl ()) (Sum.inr n) + trapBright (Sum.inl n) (Sum.inr ())) =
      1 / 2 := by
  refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · intro n
    rw [trapB_sum n]
    have := (trapB_inv_bounds n).1
    have h2 : 0 < 2 / ((n : ℝ) + 2) := by positivity
    linarith
  · intro w hw
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / (w - 1/2))
    refine ⟨n, ?_⟩
    rw [trapB_sum n]
    have hpos : 0 < w - 1/2 := by linarith
    have hn2 : 2 / (w - 1/2) < (n : ℝ) + 2 := by linarith
    have h3 : 2 / ((n : ℝ) + 2) < w - 1/2 := by
      have hden : (0:ℝ) < (n : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ hden]
      rw [div_lt_iff₀ hpos] at hn2
      linarith
    linarith

theorem trapB_cross :
    glueCrossIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright () () = 1 / 2 := by
  rw [glueCrossIInf, trapB_iInf]
  norm_num

/-- **Trap B is false.** With an infinite gluing locus the dichotomy fails: the cross
distance is `1/2`, which is neither `1` nor of the form `ω(x,z) + ω(z,y)` for any `z` in the
gluing locus. -/
theorem glue_dichotomy_infinite_false :
    ¬ (glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
          (Sum.inl ()) (Sum.inr (Sum.inr ())) = 1 ∨
        ∃ z : ℕ, glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
            (Sum.inl ()) (Sum.inr (Sum.inr ())) =
          glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
            (Sum.inl ()) (Sum.inr (Sum.inl z)) +
          glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
            (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr ()))) := by
  have hval : glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
      (Sum.inl ()) (Sum.inr (Sum.inr ())) = 1 / 2 := trapB_cross
  rintro (h | ⟨z, h⟩)
  · rw [hval] at h; norm_num at h
  · rw [hval] at h
    have : glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
        (Sum.inl ()) (Sum.inr (Sum.inl z)) +
      glueIInf (P := Unit) (Q := Unit) (F := ℕ) trapBleft trapBright
        (Sum.inr (Sum.inl z)) (Sum.inr (Sum.inr ())) = 1 / 2 + 2 / ((z : ℝ) + 2) :=
      trapB_sum z
    rw [this] at h
    have := (trapB_inv_bounds z).1
    have h2 : 0 < 2 / ((z : ℝ) + 2) := by positivity
    linarith
