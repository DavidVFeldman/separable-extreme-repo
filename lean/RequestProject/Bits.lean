import Mathlib

/-!
# Tier 6a: the canonical selectors

The canonical extension of §6 of the paper makes three choices canonically. Two of them are
selectors of a real number:

* for an **irrational** `t ∈ (0,1)`, the *canonical subdivision* of `t` is the sequence of
  gaps `(2^{-k})` for `k` running through the indices of the `1`s in the binary expansion
  of `t`, in increasing order — here `cgap t : ℕ → ℚ`, with `hasSum_cgap` saying that the
  gaps add up to `t`;
* for a **rational** `t`, the rational itself — here `ratOf t : ℚ`, which then feeds the
  bowtie family `Bowtie.bowtie (2 * (ratOf t).den)` of Tier 5.

The binary digit function is the one of the commission,
`bit t k = ⌊2^{k+1} t⌋ - 2 ⌊2^k t⌋`; it is identified with Mathlib's `Real.digits t 2` on
`[0,1)`, which supplies the summation lemma.
-/

set_option autoImplicit false

namespace Canonical

/-! ### Binary digits -/

/-- The `k`-th binary digit of a real number `t`. -/
noncomputable def bit (t : ℝ) (k : ℕ) : ℤ := ⌊2 ^ (k + 1) * t⌋ - 2 * ⌊2 ^ k * t⌋

theorem floor_two_mul (x : ℝ) : ⌊2 * x⌋ = 2 * ⌊x⌋ ∨ ⌊2 * x⌋ = 2 * ⌊x⌋ + 1 := by
  have h1 : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ := by
    rw [Int.le_floor]
    push_cast
    have := Int.floor_le x
    linarith
  have h2 : ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by
    rw [Int.floor_lt]
    push_cast
    have := Int.lt_floor_add_one x
    linarith
  omega

/-- Binary digits take the values `0` and `1`. -/
theorem bit_mem (t : ℝ) (k : ℕ) : bit t k = 0 ∨ bit t k = 1 := by
  have h : (2 : ℝ) ^ (k + 1) * t = 2 * (2 ^ k * t) := by ring
  rcases floor_two_mul ((2 : ℝ) ^ k * t) with h1 | h1 <;> simp [bit, h, h1]

theorem bit_nonneg (t : ℝ) (k : ℕ) : 0 ≤ bit t k := by
  rcases bit_mem t k with h | h <;> omega

/-- The digit function of the commission agrees with Mathlib's `Real.digits _ 2`. -/
theorem bit_eq_digits {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    bit t k = ((Real.digits t 2 k : ℕ) : ℤ) := by
  have hcast : ∀ m : ℕ, ⌊(2 : ℝ) ^ m * t⌋ = (⌊t * 2 ^ m⌋₊ : ℤ) := by
    intro m
    rw [Int.natCast_floor_eq_floor (by positivity)]
    ring_nf
  have hdiv : ⌊t * (2 : ℝ) ^ k⌋₊ = ⌊t * 2 ^ (k + 1)⌋₊ / 2 := by
    have h : t * (2 : ℝ) ^ k = (t * 2 ^ (k + 1)) / (2 : ℕ) := by push_cast; ring
    rw [h, Nat.floor_div_natCast]
  simp only [bit, hcast, hdiv]
  have hval : ((Real.digits t 2 k : ℕ) : ℤ) = ((⌊t * 2 ^ (k + 1)⌋₊ % 2 : ℕ) : ℤ) := by
    simp [Real.digits]
  rw [hval]
  have := Nat.div_add_mod (⌊t * (2 : ℝ) ^ (k + 1)⌋₊) 2
  push_cast
  omega

/-- The binary expansion of `t ∈ [0,1)` sums to `t`. -/
theorem hasSum_bits {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (fun k => (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1)) t := by
  have h := Real.hasSum_ofDigitsTerm_digits t (b := 2) (by norm_num) ⟨h0, h1⟩
  convert h using 2 with k
  rw [Real.ofDigitsTerm, bit_eq_digits h0 k]
  push_cast
  rw [inv_pow]

/-- An irrational number of `(0,1)` has infinitely many binary digits equal to `1`. -/
theorem bits_infinite {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (hirr : Irrational t) :
    {k | bit t k = 1}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hsum := hasSum_bits h0.le h1
  set S : Finset ℕ := hfin.toFinset with hS
  have hzero : ∀ k ∉ S, (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) = 0 := by
    intro k hk
    have hne : bit t k ≠ 1 := fun h => hk (by simp [hS, h])
    rcases bit_mem t k with h | h
    · simp [h]
    · exact absurd h hne
  have heq : t = ∑ k ∈ S, (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) :=
    hsum.unique (hasSum_sum_of_ne_finset_zero hzero)
  refine hirr ⟨∑ k ∈ S, (bit t k : ℚ) * (2⁻¹ : ℚ) ^ (k + 1), ?_⟩
  have hcast : ((∑ k ∈ S, (bit t k : ℚ) * (2⁻¹ : ℚ) ^ (k + 1) : ℚ) : ℝ)
      = ∑ k ∈ S, (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) := by push_cast; ring
  exact hcast.trans heq.symm

/-! ### The canonical subdivision of an irrational number -/

/-- The index of the `j`-th `1` in the binary expansion of `t`. -/
noncomputable def gapIdx (t : ℝ) (j : ℕ) : ℕ := Nat.nth (fun k => bit t k = 1) j

/-- The `j`-th *canonical gap* of `t`: the `j`-th nonzero term of its binary expansion. -/
noncomputable def cgap (t : ℝ) (j : ℕ) : ℚ := (2⁻¹ : ℚ) ^ (gapIdx t j + 1)

theorem cgap_pos (t : ℝ) (j : ℕ) : 0 < cgap t j := by
  simp only [cgap]; positivity

theorem cgap_le_one (t : ℝ) (j : ℕ) : cgap t j ≤ 1 := by
  simp only [cgap]
  apply pow_le_one₀ <;> norm_num

/-- **The canonical subdivision.** For irrational `t ∈ (0,1)` the canonical gaps are
positive rationals adding up to `t`. -/
theorem hasSum_cgap {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (hirr : Irrational t) :
    HasSum (fun j => (cgap t j : ℝ)) t := by
  have hinf := bits_infinite h0 h1 hirr
  have hinj : Function.Injective (gapIdx t) := Nat.nth_injective hinf
  have hr : Set.range (gapIdx t) = {k | bit t k = 1} := Nat.range_nth_of_infinite hinf
  have hout : ∀ k ∉ Set.range (gapIdx t), (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1) = 0 := by
    intro k hk
    have hne : ¬ bit t k = 1 := fun h => hk (by rw [hr]; exact h)
    rcases bit_mem t k with h | h
    · simp [h]
    · exact absurd h hne
  have hfin := (hinj.hasSum_iff (f := fun k => (bit t k : ℝ) * (2⁻¹ : ℝ) ^ (k + 1)) hout).mpr
    (hasSum_bits h0.le h1)
  have hcongr : ∀ j,
      (bit t (gapIdx t j) : ℝ) * (2⁻¹ : ℝ) ^ (gapIdx t j + 1) = (cgap t j : ℝ) := by
    intro j
    have hone : bit t (gapIdx t j) = 1 := Nat.nth_mem_of_infinite hinf j
    rw [hone, cgap]; push_cast; ring
  simpa only [Function.comp_def, hcongr] using hfin

/-! ### The canonical rational -/

/-- The rational number a non-irrational real is the cast of (and `0` otherwise). It is a
genuine function of the real number, so it can serve as a canonical selector. -/
noncomputable def ratOf (t : ℝ) : ℚ :=
  open Classical in
  if h : ∃ q : ℚ, (q : ℝ) = t then h.choose else 0

theorem ratOf_spec {t : ℝ} (h : ¬ Irrational t) : ((ratOf t : ℚ) : ℝ) = t := by
  have hex : ∃ q : ℚ, (q : ℝ) = t := by
    rw [Irrational, not_not] at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq⟩
  rw [ratOf, dif_pos (h := Classical.propDecidable _) hex]
  exact hex.choose_spec

/-- The canonical rational of a rational cast is that rational. -/
@[simp] theorem ratOf_cast (q : ℚ) : ratOf (q : ℝ) = q := by
  have h : ¬ Irrational (q : ℝ) := by
    rw [Irrational, not_not]
    exact ⟨q, rfl⟩
  have := ratOf_spec h
  exact_mod_cast this

end Canonical
