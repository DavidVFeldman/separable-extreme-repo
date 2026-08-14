import RequestProject.Canonical
import RequestProject.StageIsolation

/-!
# Tier 6c: isolation, limits, and recovery

The decoration points of `E(A)` — the points of the canonical chains and of the canonical
bowties — are *isolated*: each has an explicit radius inside which there is no other point
at all (Lemma 7.3 of the paper). The points of the core `A` are *not* isolated as soon as
every point of `A` has a partner at irrational distance: the canonical chain of the ordered
pair `(a', a)` accumulates at `a`.

Consequently the core is exactly the set of non-isolated points, and a surjective isometry
`E(A) → E(B)` must carry core onto core; restricting it gives the recovery theorem in the
carrier form of the commission (no completions).

The isolation predicate is stated in the form appropriate to a pseudometric,
`∃ δ > 0, ∀ y, EDist x y < δ → EDist x y = 0`; for the decoration points we in fact prove
the stronger literal form `∀ y ≠ x, δ ≤ EDist x y`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Canonical

universe u

variable {A : Type u} {d : A → A → ℝ}

/-- The decoration points of `E(A)`: the points that are not in the core. -/
def Decor (A : Type u) (d : A → A → ℝ) : Set (ECarrier A d) := {x | ¬ ∃ a, x = einl d a}

/-- The isolation predicate, in the form appropriate to a pseudometric. -/
def EIsolated (d : A → A → ℝ) (x : ECarrier A d) : Prop :=
  ∃ δ > 0, ∀ y, EDist d x y < δ → EDist d x y = 0

/-- The reciprocal of the size of the bowtie glued onto the target pair `j`. -/
noncomputable def invb (d : A → A → ℝ) (j : Bows A d) : ℝ :=
  (((Stage2.bsz (dist1 d) (banc d) j : ℕ) : ℝ))⁻¹

theorem invb_pos (j : Bows A d) : 0 < invb d j := by
  have h : 2 ≤ Stage2.bsz (dist1 d) (banc d) j :=
    Stage2.two_le_bsz (D := dist1 d) (banc := banc d) j
  have h2 : (0 : ℝ) < ((Stage2.bsz (dist1 d) (banc d) j : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((Stage2.bsz (dist1 d) (banc d) j : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  simpa [invb] using inv_pos.mpr h2

/-- The isolation radius of the `n`-th new point of the canonical chain over `p`: the
stage-1 radius, together with the sizes of the four bowties anchored at the point. -/
noncomputable def chainDelta (d : A → A → ℝ) (p : Chains A d) (n : ℕ) : ℝ :=
  min (Stage1.cdel d (cu d) (cv d) (cgaps d) p n)
    (min (min (invb d (Sum.inr (p, n, false))) (invb d (Sum.inr (p, n, true))))
      (min (invb d (Sum.inr (p, n + 1, false))) (invb d (Sum.inr (p, n + 1, true)))))

section

variable (hd : IsBddPseudo d)

include hd

theorem chainDelta_pos (p : Chains A d) (n : ℕ) : 0 < chainDelta d p n := by
  have h := Stage1.cdel_pos (a := cgaps d) (cgaps_pos d) (cgaps_hasSum hd) p n
  simp only [chainDelta, lt_min_iff]
  exact ⟨h, ⟨invb_pos _, invb_pos _⟩, invb_pos _, invb_pos _⟩

theorem chainDelta_le_one (p : Chains A d) (n : ℕ) : chainDelta d p n ≤ 1 :=
  le_trans (min_le_left _ _)
    (Stage1.cdel_le_one hd (cgaps_pos d) (cgaps_hasSum hd) p n)

omit hd in
/-- Identification of the targets anchored at a chain point: if an anchor of the bowtie of
the target `j` is the `n`-th new point of the chain over `p`, then `j` is one of the four
gap pairs adjacent to that point. -/
theorem banc_eq_chain (p : Chains A d) (n : ℕ) (j : Bows A d) (l : Bool)
    (h : banc d j l = Sum.inr (p, n)) : chainDelta d p n ≤ invb d j := by
  match j with
  | Sum.inl q =>
      exfalso
      cases l
      · exact Sum.inl_ne_inr (show (Sum.inl q.val.1 : W1 A d) = Sum.inr (p, n) from h)
      · exact Sum.inl_ne_inr (show (Sum.inl q.val.2 : W1 A d) = Sum.inr (p, n) from h)
  | Sum.inr (p', m, o) =>
      have h' : chp d p' (if l = o then m else m + 1) = Sum.inr (p, n) := h
      have hk : ∀ k : ℕ, chp d p' k = Sum.inr (p, n) → p' = p ∧ k = n + 1 := by
        intro k hkk
        match k with
        | 0 => exact absurd hkk (by simp [chp, Stage1.chainPt])
        | (k + 1) =>
            have h2 : (p', k) = (p, n) := by simpa [chp, Stage1.chainPt] using hkk
            refine ⟨congrArg Prod.fst h2, ?_⟩
            have h3 : k = n := congrArg Prod.snd h2
            omega
      obtain ⟨hp', hk'⟩ := hk _ h'
      subst hp'
      by_cases hlo : l = o
      · rw [if_pos hlo] at hk'
        subst hk'
        cases o
        · exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        · exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
      · rw [if_neg hlo] at hk'
        have hm : m = n := by omega
        subst hm
        cases o
        · exact le_trans (min_le_right _ _)
            (le_trans (min_le_left _ _) (min_le_left _ _))
        · exact le_trans (min_le_right _ _)
            (le_trans (min_le_left _ _) (min_le_right _ _))

/-- **A new point of a canonical chain is isolated in `E(A)`.** -/
theorem E_chain_isolated (p : Chains A d) (n : ℕ) {y : ECarrier A d}
    (hy : y ≠ Sum.inl (Sum.inr (p, n))) :
    chainDelta d p n ≤ EDist d (Sum.inl (Sum.inr (p, n))) y := by
  classical
  have hd1 : IsBddPseudo (dist1 d) := dist1_isBddPseudo hd
  have hq0 := banc_pos hd
  have hrat := banc_rat hd
  refine glueFamily_base_isolated (chainDelta_le_one hd p n) (Sum.inr (p, n)) ?_ ?_ hy
  · intro w'
    by_cases hw : w' = Sum.inr (p, n)
    · exact Or.inl hw
    · exact Or.inr (le_trans (min_le_left _ _)
        (Stage1.subDist_chain_isolated hd (cgaps_pos d) (cgaps_hasSum hd) p n hw))
  · intro z l
    have hs0 : 0 ≤ dist1 d (Sum.inr (p, n)) (banc d (Stage2.dIdx z) l) := hd1.nonneg _ _
    by_cases hb : banc d (Stage2.dIdx z) l = Sum.inr (p, n)
    · have h1 := banc_eq_chain p n (Stage2.dIdx z) l hb
      have h2 := Stage2.inv_bsz_le_pieceAnc hd1 hq0 hrat z l
      have h3 : invb d (Stage2.dIdx z) ≤
          Stage2.pieceDist (dist1 d) (banc d) (Stage2.dIdx z) (Stage2.dPos z)
            (Stage2.pieceAnc (dist1 d) (banc d) (Stage2.dIdx z) l) := h2
      linarith
    · have h1 : Stage1.cdel d (cu d) (cv d) (cgaps d) p n ≤
          dist1 d (Sum.inr (p, n)) (banc d (Stage2.dIdx z) l) :=
        Stage1.subDist_chain_isolated hd (cgaps_pos d) (cgaps_hasSum hd) p n
          (fun hc => hb hc)
      have h2 : chainDelta d p n ≤ Stage1.cdel d (cu d) (cv d) (cgaps d) p n :=
        min_le_left _ _
      have h3 : 0 ≤ Stage2.pieceDist (dist1 d) (banc d) (Stage2.dIdx z) (Stage2.dPos z)
          (Stage2.pieceAnc (dist1 d) (banc d) (Stage2.dIdx z) l) :=
        (Stage2.pieceDist_isBddPseudo (D := dist1 d) (banc := banc d) (Stage2.dIdx z)).nonneg _ _
      linarith

/-- **The decoration points of `E(A)` are isolated**, with an explicit radius: no other
point of `E(A)` is nearer than that radius. -/
theorem decor_isolated : ∀ x ∈ Decor A d, ∃ δ > 0, ∀ y, y ≠ x → δ ≤ EDist d x y := by
  rintro (w | z) hx
  · match w with
    | Sum.inl a => exact absurd ⟨a, rfl⟩ hx
    | Sum.inr (p, n) =>
        exact ⟨chainDelta d p n, chainDelta_pos hd p n, fun y hy => E_chain_isolated hd p n hy⟩
  · refine ⟨invb d (Stage2.dIdx z), invb_pos _, fun y hy => ?_⟩
    exact Stage2.frzDist_decor_isolated (dist1_isBddPseudo hd) (banc_pos hd) (banc_rat hd) z hy

/-- The decoration points are isolated in the pseudometric sense. -/
theorem decor_EIsolated {x : ECarrier A d} (hx : x ∈ Decor A d) : EIsolated d x := by
  obtain ⟨δ, hδ, hx'⟩ := decor_isolated hd x hx
  refine ⟨δ, hδ, fun y hy => ?_⟩
  by_cases hxy : y = x
  · subst hxy
    exact (E_isBddPseudo hd).diag _
  · exact absurd (hx' y hxy) (by linarith)

end

/-! ### The core points are limits of decoration points -/

section

variable (hd : IsBddPseudo d) (hirr : ∀ a : A, ∃ a', Irrational (d a a'))

include hd hirr

/-- **Every core point is a limit of decoration points**: the canonical chain of the
ordered pair `(a', a)`, for a partner `a'` at irrational distance, accumulates at `a`. -/
theorem core_is_limit (a : A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q ∈ Decor A d, 0 < EDist d (einl d a) q ∧ EDist d (einl d a) q < δ := by
  obtain ⟨a', ha'⟩ := hirr a
  have hsymm : d a' a = d a a' := hd.symm _ _
  have hirr' : Irrational (d a' a) := by rw [hsymm]; exact ha'
  set p : Chains A d := ⟨(a', a), hirr'⟩ with hp
  have hcu : cu d p = a' := rfl
  have hcv : cv d p = a := rfl
  -- the partial sums of the canonical gaps converge to the distance
  have hsum := cgaps_hasSum hd p
  have htend := hsum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend δ hδ
  have hNN := hN (N + 1) (by omega)
  have hspos : Stage1.spos (cgaps d) p (N + 1) = ∑ i ∈ Finset.range (N + 1), cgaps d p i := rfl
  have hlt : Stage1.spos (cgaps d) p (N + 1) < d (cu d p) (cv d p) :=
    Stage1.spos_lt (cgaps_pos d) (cgaps_hasSum hd) p (N + 1)
  have hclose : d (cu d p) (cv d p) - Stage1.spos (cgaps d) p (N + 1) < δ := by
    rw [Real.dist_eq] at hNN
    rw [hspos]
    have := abs_lt.mp hNN
    linarith [this.1, this.2]
  -- the `N`-th new point of the chain is the required decoration point
  refine ⟨Sum.inl (Sum.inr (p, N)), ?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    simp only [einl] at hb
    exact Sum.inr_ne_inl (Sum.inl_injective hb)
  · have h : EDist d (einl d a) (Sum.inl (Sum.inr (p, N)))
        = d (cu d p) (cv d p) - Stage1.spos (cgaps d) p (N + 1) := by
      have htail := Stage1.subDist_tail hd (cgaps_pos d) (cgaps_hasSum hd) (a := cgaps d)
        (tu := cu d) (tv := cv d) p (N + 1)
      have hsymm1 := (dist1_isBddPseudo hd).symm
      show dist1 d (Sum.inl a) (Sum.inr (p, N)) = _
      rw [hsymm1]
      exact htail
    rw [h]; linarith
  · have h : EDist d (einl d a) (Sum.inl (Sum.inr (p, N)))
        = d (cu d p) (cv d p) - Stage1.spos (cgaps d) p (N + 1) := by
      have htail := Stage1.subDist_tail hd (cgaps_pos d) (cgaps_hasSum hd) (a := cgaps d)
        (tu := cu d) (tv := cv d) p (N + 1)
      have hsymm1 := (dist1_isBddPseudo hd).symm
      show dist1 d (Sum.inl a) (Sum.inr (p, N)) = _
      rw [hsymm1]
      exact htail
    rw [h]; exact hclose

/-- **No core point is isolated.** -/
theorem core_not_EIsolated (a : A) : ¬ EIsolated d (einl d a) := by
  rintro ⟨δ, hδ, hiso⟩
  obtain ⟨q, -, hq0, hq1⟩ := core_is_limit hd hirr a hδ
  exact absurd (hiso q hq1) (ne_of_gt hq0)

end

/-! ### Recovery -/

theorem einl_injective : Function.Injective (einl d) := by
  intro a a' h
  exact Sum.inl.inj (Sum.inl.inj h)

/-- **Recovery, carrier form** (the commission's (R)): a surjective isometry of the
canonical extensions restricts to a distance-preserving bijection of the cores, provided
every point of either core has a partner at irrational distance. -/
theorem recovery {B : Type u} {dA : A → A → ℝ} {dB : B → B → ℝ}
    (hdA : IsBddPseudo dA) (hdB : IsBddPseudo dB)
    (hirrA : ∀ a : A, ∃ a', Irrational (dA a a')) (hirrB : ∀ b : B, ∃ b', Irrational (dB b b'))
    (Φ : ECarrier A dA → ECarrier B dB) (hbij : Function.Bijective Φ)
    (hiso : ∀ x y, EDist dB (Φ x) (Φ y) = EDist dA x y) :
    ∃ φ : A → B, Function.Bijective φ ∧ (∀ a a', dB (φ a) (φ a') = dA a a') ∧
      ∀ a, Φ (einl dA a) = einl dB (φ a) := by
  classical
  -- the image of a core point is a core point
  have key : ∀ a : A, ∃ b : B, Φ (einl dA a) = einl dB b := by
    intro a
    by_contra hcon
    have hdec : Φ (einl dA a) ∈ Decor B dB := hcon
    obtain ⟨δ, hδ, hd'⟩ := decor_EIsolated hdB hdec
    refine core_not_EIsolated hdA hirrA a ⟨δ, hδ, fun y hy => ?_⟩
    have h1 : EDist dB (Φ (einl dA a)) (Φ y) = EDist dA (einl dA a) y := hiso _ _
    rw [← h1] at hy ⊢
    exact hd' (Φ y) hy
  choose φ hφ using key
  have hisoφ : ∀ a a', dB (φ a) (φ a') = dA a a' := by
    intro a a'
    have h1 : EDist dB (einl dB (φ a)) (einl dB (φ a')) = EDist dA (einl dA a) (einl dA a') := by
      rw [← hφ a, ← hφ a']
      exact hiso _ _
    simpa only [E_extends] using h1
  refine ⟨φ, ⟨?_, ?_⟩, hisoφ, hφ⟩
  · intro a a' h
    have h1 : Φ (einl dA a) = Φ (einl dA a') := by rw [hφ a, hφ a', h]
    exact einl_injective (hbij.1 h1)
  · intro b
    obtain ⟨x, hx⟩ := hbij.2 (einl dB b)
    have hxcore : ∃ a : A, x = einl dA a := by
      by_contra hcon
      have hdec : x ∈ Decor A dA := hcon
      obtain ⟨δ, hδ, hd'⟩ := decor_EIsolated hdA hdec
      refine core_not_EIsolated hdB hirrB b ⟨δ, hδ, fun y hy => ?_⟩
      obtain ⟨y', rfl⟩ := hbij.2 y
      have h1 : EDist dB (Φ x) (Φ y') = EDist dA x y' := hiso _ _
      rw [hx] at h1
      rw [h1] at hy ⊢
      exact hd' y' hy
    obtain ⟨a, rfl⟩ := hxcore
    exact ⟨a, einl_injective (by rw [← hφ a, hx])⟩

end Canonical
