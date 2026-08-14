import RequestProject.Subdivision
import RequestProject.GlueTransport

/-!
# Stage 1 of the canonical extension, on an explicit carrier

`Subdivision.lean` produces the stage-1 amalgam existentially (`∃ ω, …`). The canonical
extension of §6 needs the *same* construction with a name: the carrier is `X ⊕ T × ℕ`, the
distance is `subDist d tu tv a`, and the gaps `a` are supplied by the caller (for the
canonical extension they will be the canonical gaps of `Bits.lean`).

Everything here is the content of `exists_subdivision_extension`, restated for the explicit
carrier and proved the same way.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Stage1

variable {X T : Type*}

/-- Partial sums of the gaps of the chain over the pair `p`. -/
def spos (a : T → ℕ → ℝ) (p : T) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, a p i

/-- The position of the `n`-th new point of the chain over `p`. -/
def ppos (a : T → ℕ → ℝ) (y : T × ℕ) : ℝ := spos a y.1 (y.2 + 1)

/-- The two anchors of the chain over `p`. -/
def anch (tu tv : T → X) (p : T) (b : Bool) : X := if b then tv p else tu p

/-- The positions of the two anchors of the chain over `p`. -/
def qval (d : X → X → ℝ) (tu tv : T → X) (p : T) (b : Bool) : ℝ :=
  if b then d (tu p) (tv p) else 0

/-- The stage-1 amalgam: the chains over all the pairs `(tu p, tv p)`, glued at once. -/
noncomputable def subDist (d : X → X → ℝ) (tu tv : T → X) (a : T → ℕ → ℝ) :
    (X ⊕ T × ℕ) → (X ⊕ T × ℕ) → ℝ :=
  open Classical in
  glueFamily d (Prod.fst : T × ℕ → T) (anch tu tv)
    (fun y y' => |ppos a y - ppos a y'|)
    (fun y l => |ppos a y - qval d tu tv y.1 l|)

/-- The chain over `p`: the point `0` is the anchor `tu p`, the point `n+1` is the `n`-th
new point. -/
def chainPt (tu : T → X) : T → ℕ → (X ⊕ T × ℕ)
  | p, 0 => Sum.inl (tu p)
  | p, (n + 1) => Sum.inr (p, n)

@[simp] theorem chainPt_zero (tu : T → X) (p : T) : chainPt tu p 0 = Sum.inl (tu p) := rfl

@[simp] theorem chainPt_succ (tu : T → X) (p : T) (n : ℕ) :
    chainPt tu p (n + 1) = Sum.inr (p, n) := rfl

theorem spos_zero (a : T → ℕ → ℝ) (p : T) : spos a p 0 = 0 := by simp [spos]

theorem spos_succ (a : T → ℕ → ℝ) (p : T) (j : ℕ) :
    spos a p (j + 1) = spos a p j + a p j := by
  simp [spos, Finset.sum_range_succ]

section

variable {d : X → X → ℝ} {tu tv : T → X} {a : T → ℕ → ℝ}
  (hd : IsBddPseudo d) (hapos : ∀ p i, 0 < a p i)
  (hasum : ∀ p, HasSum (fun i => a p i) (d (tu p) (tv p)))

include hapos

theorem spos_nonneg (p : T) (j : ℕ) : 0 ≤ spos a p j :=
  Finset.sum_nonneg fun i _ => (hapos p i).le

omit hapos in
theorem spos_seg (p : T) (j m : ℕ) :
    spos a p (j + m) - spos a p j = ∑ i ∈ Finset.range m, a p (j + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have e : spos a p (j + (m + 1)) = spos a p (j + m) + a p (j + m) := by
        have hjm : j + (m + 1) = (j + m) + 1 := by omega
        rw [hjm, spos_succ a]
      rw [e, Finset.sum_range_succ, ← ih]; ring

theorem spos_mono (p : T) {j k : ℕ} (hjk : j ≤ k) : spos a p j ≤ spos a p k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have h := spos_seg (a := a) p j m
  have hnn : (0:ℝ) ≤ ∑ i ∈ Finset.range m, a p (j + i) :=
    Finset.sum_nonneg fun i _ => (hapos p (j + i)).le
  linarith

include hasum

theorem spos_lt (p : T) (j : ℕ) : spos a p j < d (tu p) (tv p) := by
  have h1 : spos a p (j + 1) ≤ d (tu p) (tv p) :=
    sum_le_hasSum (Finset.range (j + 1)) (fun i _ => (hapos p i).le) (hasum p)
  have := spos_succ a p j
  have := hapos p j
  simp only [spos] at *
  linarith

theorem dist_pos (p : T) : 0 < d (tu p) (tv p) := by
  have := spos_lt hapos hasum p 0
  rw [spos_zero a] at this
  exact this

include hd

theorem piece_data :
    IsPieceData d (Prod.fst : T × ℕ → T) (anch tu tv)
      (fun y y' => |ppos a y - ppos a y'|)
      (fun y l => |ppos a y - qval d tu tv y.1 l|) := by
  have hgd : ∀ (p : T) (b b' : Bool),
      d (anch tu tv p b) (anch tu tv p b') = |qval d tu tv p b - qval d tu tv p b'| := by
    intro p b b'
    have h0 : (0 : ℝ) ≤ d (tu p) (tv p) := (dist_pos hapos hasum p).le
    have hdvu : d (tv p) (tu p) = d (tu p) (tv p) := hd.symm _ _
    cases b <;> cases b' <;>
      simp only [anch, qval, if_true, if_false, Bool.false_eq_true]
    · rw [hd.diag]; simp
    · rw [zero_sub, abs_neg, abs_of_nonneg h0]
    · rw [hdvu, sub_zero, abs_of_nonneg h0]
    · rw [hd.diag]; simp
  have hP0 : ∀ y : T × ℕ, 0 ≤ ppos a y := fun y => spos_nonneg hapos _ _
  have hP1 : ∀ y : T × ℕ, ppos a y ≤ 1 := by
    intro y
    have h1 := spos_lt hapos hasum y.1 (y.2 + 1)
    have h2 := hd.le_one (tu y.1) (tv y.1)
    simp only [ppos]
    linarith
  have hQ0 : ∀ (p : T) (b : Bool), 0 ≤ qval d tu tv p b := by
    intro p b
    cases b <;> simp only [qval, if_true, if_false, Bool.false_eq_true, le_refl]
    exact (dist_pos hapos hasum p).le
  have hQ1 : ∀ (p : T) (b : Bool), qval d tu tv p b ≤ 1 := by
    intro p b
    cases b <;> simp only [qval, if_true, if_false, Bool.false_eq_true]
    · norm_num
    · exact hd.le_one _ _
  exact isPieceData_of_real d (Prod.fst : T × ℕ → T) (anch tu tv) (ppos a)
    (qval d tu tv) hP0 hP1 hQ0 hQ1 hgd

theorem subDist_isBddPseudo : IsBddPseudo (subDist d tu tv a) := by
  classical
  exact glueFamily_isBddPseudo hd (piece_data hd hapos hasum)

omit hd hapos hasum in
@[simp] theorem subDist_base (x x' : X) :
    subDist d tu tv a (Sum.inl x) (Sum.inl x') = d x x' := rfl

theorem subDist_locus (p : T) (n : ℕ) (l : Bool) :
    subDist d tu tv a (Sum.inl (anch tu tv p l)) (Sum.inr (p, n))
      = |ppos a (p, n) - qval d tu tv p l| := by
  classical
  exact glueFamily_restrict_locus hd (piece_data hd hapos hasum) (p, n) l

omit hd hapos hasum in
theorem subDist_piece (p : T) (n n' : ℕ) :
    subDist d tu tv a (Sum.inr (p, n)) (Sum.inr (p, n'))
      = |ppos a (p, n) - ppos a (p, n')| := by
  classical
  exact glueFamily_restrict_piece (d := d) (idx := (Prod.fst : T × ℕ → T)) rfl

/-- The distance between two points of the same chain. -/
theorem subDist_chain (p : T) (j k : ℕ) :
    subDist d tu tv a (chainPt tu p j) (chainPt tu p k) = |spos a p j - spos a p k| := by
  have hbdd := subDist_isBddPseudo hd hapos hasum (tu := tu) (tv := tv) (a := a)
  match j, k with
  | 0, 0 => rw [hbdd.diag]; simp
  | 0, (m + 1) =>
      have h := subDist_locus hd hapos hasum (a := a) p m false
      simp only [anch, if_false, Bool.false_eq_true] at h
      rw [chainPt_zero, chainPt_succ, h]
      simp only [ppos, qval, if_false, Bool.false_eq_true, sub_zero, spos_zero a, zero_sub,
        abs_neg]
  | (n + 1), 0 =>
      have h := subDist_locus hd hapos hasum (a := a) p n false
      simp only [anch, if_false, Bool.false_eq_true] at h
      rw [chainPt_zero, chainPt_succ, hbdd.symm, h]
      simp only [ppos, qval, if_false, Bool.false_eq_true, sub_zero, spos_zero a]
  | (n + 1), (m + 1) =>
      rw [chainPt_succ, chainPt_succ, subDist_piece]
      simp only [ppos]

/-- The gaps of the chain are the given rationals. -/
theorem subDist_gap (p : T) (i : ℕ) :
    subDist d tu tv a (chainPt tu p i) (chainPt tu p (i + 1)) = a p i := by
  rw [subDist_chain hd hapos hasum, spos_succ a,
    abs_of_nonpos (by linarith [hapos p i])]
  ring

/-- The distance from the initial anchor to the `j`-th point of the chain. -/
theorem subDist_pre (p : T) (j : ℕ) :
    subDist d tu tv a (chainPt tu p 0) (chainPt tu p j) = spos a p j := by
  rw [subDist_chain hd hapos hasum, spos_zero a, zero_sub, abs_neg,
    abs_of_nonneg (spos_nonneg hapos p j)]

/-- The distance from the `j`-th point of the chain to the terminal anchor. -/
theorem subDist_tail (p : T) (j : ℕ) :
    subDist d tu tv a (chainPt tu p j) (Sum.inl (tv p))
      = d (tu p) (tv p) - spos a p j := by
  have hbdd := subDist_isBddPseudo hd hapos hasum (tu := tu) (tv := tv) (a := a)
  match j with
  | 0 => rw [chainPt_zero, spos_zero a, sub_zero]; rfl
  | (n + 1) =>
      have h := subDist_locus hd hapos hasum (a := a) p n true
      simp only [anch, if_true] at h
      rw [chainPt_succ, hbdd.symm, h]
      simp only [ppos, qval, if_true]
      rw [abs_of_nonpos (by linarith [spos_lt hapos hasum p (n + 1)])]
      ring

/-! ### Rigidity transfer -/

/-- A perturbation of the stage-1 amalgam which vanishes on the base and on all the gaps
vanishes identically. -/
theorem subDist_rigid_transfer (E : (X ⊕ T × ℕ) → (X ⊕ T × ℕ) → ℝ)
    (hE : IsPerturbation (subDist d tu tv a) E)
    (hgaps : ∀ p i, E (chainPt tu p i) (chainPt tu p (i + 1)) = 0)
    (hbaseE : ∀ x x', E (Sum.inl x) (Sum.inl x') = 0) : ∀ w w', E w w' = 0 := by
  classical
  set ω := subDist d tu tv a with hω
  have hp := piece_data hd hapos hasum (tu := tu) (tv := tv) (a := a)
  have hgap := subDist_gap hd hapos hasum (tu := tu) (tv := tv) (a := a)
  -- perturbations vanish along each chain
  have hchainseg : ∀ (p : T) (j m : ℕ),
      E (chainPt tu p j) (chainPt tu p (j + m)) = 0 := by
    intro p j m
    have htight : ω (chainPt tu p j) (chainPt tu p (j + m)) =
        ∑ i ∈ Finset.range m, ω (chainPt tu p (j + i)) (chainPt tu p (j + i + 1)) := by
      have hl : ω (chainPt tu p j) (chainPt tu p (j + m)) = spos a p (j + m) - spos a p j := by
        rw [hω, subDist_chain hd hapos hasum,
          abs_of_nonpos (by linarith [spos_mono hapos p (Nat.le_add_right j m)])]
        ring
      have hr : ∑ i ∈ Finset.range m, ω (chainPt tu p (j + i)) (chainPt tu p (j + i + 1)) =
          ∑ i ∈ Finset.range m, a p (j + i) :=
        Finset.sum_congr rfl fun i _ => hgap p (j + i)
      rw [hl, hr, spos_seg]
    have hsum : E (chainPt tu p j) (chainPt tu p (j + m)) =
        ∑ i ∈ Finset.range m, E (chainPt tu p (j + i)) (chainPt tu p (j + i + 1)) :=
      pert_add_of_tight_chain ω E hE (fun i => chainPt tu p (j + i)) htight
    rw [hsum]
    exact Finset.sum_eq_zero fun i _ => hgaps p (j + i)
  have hchain : ∀ (p : T) (j k : ℕ), E (chainPt tu p j) (chainPt tu p k) = 0 := by
    intro p j k
    rcases le_total j k with h | h
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hchainseg p j m
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [hE.1]
      exact hchainseg p k m
  have hchaintv : ∀ (p : T) (j : ℕ), E (chainPt tu p j) (Sum.inl (tv p)) = 0 := by
    intro p j
    have htight : ω (chainPt tu p 0) (Sum.inl (tv p)) =
        ω (chainPt tu p 0) (chainPt tu p j) + ω (chainPt tu p j) (Sum.inl (tv p)) := by
      rw [hω, subDist_tail hd hapos hasum, subDist_tail hd hapos hasum,
        subDist_pre hd hapos hasum, spos_zero a]
      ring
    have h := pert_add_of_tight ω E hE htight
    have h0 : E (chainPt tu p 0) (Sum.inl (tv p)) = 0 := by
      rw [chainPt_zero]; exact hbaseE _ _
    have h1 : E (chainPt tu p 0) (chainPt tu p j) = 0 := hchain p 0 j
    linarith
  have hchaintu : ∀ (p : T) (j : ℕ), E (chainPt tu p j) (Sum.inl (tu p)) = 0 := by
    intro p j
    rw [hE.1, ← chainPt_zero tu p]
    exact hchain p 0 j
  have hanch : ∀ (p : T) (n : ℕ) (l : Bool),
      E (Sum.inl (anch tu tv p l)) (Sum.inr (p, n)) = 0 := by
    intro p n l
    cases l
    · simp only [anch, if_false, Bool.false_eq_true]
      rw [hE.1, ← chainPt_succ tu p n]
      exact hchaintu p (n + 1)
    · simp only [anch, if_true]
      rw [hE.1, ← chainPt_succ tu p n]
      exact hchaintv p (n + 1)
  -- cross pairs base–chain
  have hcross : ∀ (x : X) (y : T × ℕ), E (Sum.inl x) (Sum.inr y) = 0 := by
    rintro x ⟨p, n⟩
    rcases glueFamily_dichotomy_base_piece hd hp x (p, n) with h1 | ⟨l, h1⟩
    · exact pert_eq_zero_of_dist_eq_one hE h1
    · exact by
        rw [pert_add_of_tight ω E hE h1, hbaseE, hanch p n l, add_zero]
  rintro (x | ⟨p, n⟩) (x' | ⟨p', n'⟩)
  · exact hbaseE x x'
  · exact hcross x (p', n')
  · rw [hE.1]; exact hcross x' (p, n)
  · by_cases hpp : p = p'
    · subst hpp
      rw [← chainPt_succ tu p n, ← chainPt_succ tu p n']
      exact hchain p (n + 1) (n' + 1)
    · rcases glueFamily_dichotomy_piece_piece hd hp (y := (p, n)) (y' := (p', n')) hpp with
        h1 | ⟨l, l', h1⟩
      · exact pert_eq_zero_of_dist_eq_one hE h1
      · set q : ℕ → (X ⊕ T × ℕ) := fun k =>
          match k with
          | 0 => Sum.inr (p, n)
          | 1 => Sum.inl (anch tu tv p l)
          | 2 => Sum.inl (anch tu tv p' l')
          | _ => Sum.inr (p', n') with hq
        have htight : ω (q 0) (q 3) = ∑ i ∈ Finset.range 3, ω (q i) (q (i + 1)) := by
          simp only [hq, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          simpa using h1
        have hsum := pert_add_of_tight_chain ω E hE (m := 3) q htight
        have e0 : E (q 0) (q 1) = 0 := by
          simp only [hq]
          rw [hE.1]
          exact hanch p n l
        have e1 : E (q 1) (q 2) = 0 := by simp only [hq]; exact hbaseE _ _
        have e2 : E (q 2) (q 3) = 0 := by
          simp only [hq]
          exact hanch p' n' l'
        have hz : E (q 0) (q 3) = 0 := by
          rw [hsum]
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          rw [e0, e1, e2]; ring
        simpa [hq] using hz

end

end Stage1
