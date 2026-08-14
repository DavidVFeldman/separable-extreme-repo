import RequestProject.Canonical

/-!
# Tier 6b: functoriality of the canonical extension

Theorem 6.3 of the paper. A distance-preserving injection `ψ : A → B` induces a
distance-preserving injection `E(ψ) : E(A) → E(B)` commuting with the inclusions of the
cores, and `E` is functorial: it preserves composition, identities, and surjectivity.

The proof is pure plumbing: both stages of the canonical extension are instances of
`glueFamily`, and `glueFamily_transport` says that a map of gluing data induces an isometry
of the amalgams. All the canonical selectors — the canonical gaps of a chain, the canonical
rational, the size and the anchor level of a bowtie — are functions of *distances only*, so
they are unchanged by a distance-preserving map, and the gluing data match on the nose.
-/

set_option autoImplicit false

open scoped BigOperators

/-! ### Transport of the two stages -/

namespace Stage1

variable {X T X' T' : Type*}

/-- **Stage 1 transports along a map of subdivision data.** -/
theorem subDist_transport {d : X → X → ℝ} {tu tv : T → X} {a : T → ℕ → ℝ}
    {d' : X' → X' → ℝ} {tu' tv' : T' → X'} {a' : T' → ℕ → ℝ}
    {fX : X → X'} {fT : T → T'}
    (hfX : ∀ x y, d' (fX x) (fX y) = d x y) (hfT : Function.Injective fT)
    (htu : ∀ p, tu' (fT p) = fX (tu p)) (htv : ∀ p, tv' (fT p) = fX (tv p))
    (ha : ∀ p i, a' (fT p) i = a p i) (w w' : X ⊕ T × ℕ) :
    subDist d' tu' tv' a' (Sum.map fX (fun y => (fT y.1, y.2)) w)
        (Sum.map fX (fun y => (fT y.1, y.2)) w') = subDist d tu tv a w w' := by
  classical
  have hspos : ∀ (p : T) (j : ℕ), spos a' (fT p) j = spos a p j := by
    intro p j
    simp only [spos]
    exact Finset.sum_congr rfl fun i _ => ha p i
  have hppos : ∀ y : T × ℕ, ppos a' (fT y.1, y.2) = ppos a y := by
    intro y; simpa only [ppos] using hspos y.1 (y.2 + 1)
  refine glueFamily_transport (L := Bool) (fX := fX) (fY := fun y => (fT y.1, y.2)) (fI := fT)
    hfX ?_ hfT ?_ ?_ ?_ w w'
  · intro y; rfl
  · intro p l
    cases l
    · simpa only [anch, if_false, Bool.false_eq_true] using htu p
    · simpa only [anch, if_true] using htv p
  · intro y y' _
    rw [hppos y, hppos y']
  · intro y l
    have hq : qval d' tu' tv' (fT y.1) l = qval d tu tv y.1 l := by
      cases l
      · simp only [qval, if_false, Bool.false_eq_true]
      · simp only [qval, if_true]
        rw [htu, htv, hfX]
    rw [hppos y, hq]

end Stage1

namespace Stage2

variable {W J W' J' : Type*}

section

variable {D : W → W → ℝ} {banc : J → Bool → W} {D' : W' → W' → ℝ} {banc' : J' → Bool → W'}
  {fW : W → W'} {fJ : J → J'}
  (hfW : ∀ w w', D' (fW w) (fW w') = D w w')
  (hbanc : ∀ j l, banc' (fJ j) l = fW (banc j l))

include hfW hbanc

theorem qOf_transport (j : J) : qOf D' banc' (fJ j) = qOf D banc j := by
  simp only [qOf, hbanc, hfW]

theorem bsz_transport (j : J) : bsz D' banc' (fJ j) = bsz D banc j := by
  simp only [bsz, qOf_transport hfW hbanc]

theorem alv_transport (j : J) : alv D' banc' (fJ j) = alv D banc j := by
  simp only [alv, qOf_transport hfW hbanc]

/-- The decoration points transport. -/
def decorMap (z : Decor2 D banc) : Decor2 D' banc' :=
  ⟨(fJ z.val.1, z.val.2), by
    have hb := bsz_transport hfW hbanc z.val.1
    have hal := alv_transport hfW hbanc z.val.1
    exact ⟨by rw [hb]; exact z.property.1, by rw [hal]; exact z.property.2⟩⟩

theorem decorMap_val (z : Decor2 D banc) :
    (decorMap hfW hbanc z).val = (fJ z.val.1, z.val.2) := rfl

/-- **Stage 2 transports along a map of freezing data.** -/
theorem frzDist_transport (hfJ : Function.Injective fJ) (x y : W ⊕ Decor2 D banc) :
    frzDist D' banc' (Sum.map fW (decorMap hfW hbanc) x)
        (Sum.map fW (decorMap hfW hbanc) y) = frzDist D banc x y := by
  classical
  have hpiece : ∀ (j : J) (p q : PT),
      pieceDist D' banc' (fJ j) p q = pieceDist D banc j p q := by
    intro j p q
    simp only [pieceDist]
    rw [bsz_transport hfW hbanc j]
  have hanc : ∀ (j : J) (l : Bool),
      pieceAnc D' banc' (fJ j) l = pieceAnc D banc j l := by
    intro j l
    simp only [pieceAnc, alv_transport hfW hbanc]
  have hdIdx : ∀ z : Decor2 D banc, dIdx (decorMap hfW hbanc z) = fJ (dIdx z) := fun _ => rfl
  have hdPos : ∀ z : Decor2 D banc, dPos (decorMap hfW hbanc z) = dPos z := fun _ => rfl
  refine glueFamily_transport (L := Bool) (fX := fW) (fY := decorMap hfW hbanc) (fI := fJ)
    hfW ?_ hfJ hbanc ?_ ?_ x y
  · intro z; rfl
  · intro z z' h
    have h1 : dIdx (decorMap hfW hbanc z) = dIdx (decorMap hfW hbanc z') := by
      rw [hdIdx, hdIdx, h]
    rw [if_pos h1, if_pos h, hdIdx, hdPos, hdPos, hpiece]
  · intro z l
    rw [hdIdx, hdPos, hanc, hpiece]

end

end Stage2

/-! ### Functoriality of `E` -/

namespace Canonical

universe u

section

variable {A B : Type u} {dA : A → A → ℝ} {dB : B → B → ℝ} (ψ : A → B)
  (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')

/-- The induced map on stage-1 chain indices. -/
def cmap : Chains A dA → Chains B dB :=
  fun p => ⟨(ψ (cu dA p), ψ (cv dA p)), by rw [hψ]; exact cirr dA p⟩

@[simp] theorem cu_cmap (p : Chains A dA) : cu dB (cmap ψ hψ p) = ψ (cu dA p) := rfl

@[simp] theorem cv_cmap (p : Chains A dA) : cv dB (cmap ψ hψ p) = ψ (cv dA p) := rfl

theorem cmap_injective (hinj : Function.Injective ψ) :
    Function.Injective (cmap ψ hψ) := by
  intro p q h
  have h1 : ψ (cu dA p) = ψ (cu dA q) := congrArg (cu dB) h
  have h2 : ψ (cv dA p) = ψ (cv dA q) := congrArg (cv dB) h
  have : (cu dA p, cv dA p) = (cu dA q, cv dA q) := by
    rw [hinj h1, hinj h2]
  exact Subtype.ext this

theorem cgaps_cmap (p : Chains A dA) (i : ℕ) :
    cgaps dB (cmap ψ hψ p) i = cgaps dA p i := by
  simp only [cgaps, cu_cmap, cv_cmap, hψ]

/-- The induced map on the stage-1 carrier. -/
def w1map : W1 A dA → W1 B dB := Sum.map ψ (fun y => (cmap ψ hψ y.1, y.2))

@[simp] theorem w1map_inl (a : A) : w1map ψ hψ (Sum.inl a) = Sum.inl (ψ a) := rfl

theorem w1map_chp (p : Chains A dA) (j : ℕ) :
    w1map ψ hψ (chp dA p j) = chp dB (cmap ψ hψ p) j := by
  cases j with
  | zero => rfl
  | succ n => rfl

/-- **Stage 1 is functorial.** -/
theorem dist1_transport (hinj : Function.Injective ψ) (w w' : W1 A dA) :
    dist1 dB (w1map ψ hψ w) (w1map ψ hψ w') = dist1 dA w w' :=
  Stage1.subDist_transport (fX := ψ) (fT := cmap ψ hψ) hψ (cmap_injective ψ hψ hinj)
    (fun _ => rfl) (fun _ => rfl) (cgaps_cmap ψ hψ) w w'

theorem w1map_injective (hinj : Function.Injective ψ) :
    Function.Injective (w1map ψ hψ) := by
  refine Function.Injective.sumMap hinj ?_
  intro y y' h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (cmap_injective ψ hψ hinj h.1) h.2

/-- The induced map on rational-distance core pairs. -/
def ratmap : RatPairs A dA → RatPairs B dB :=
  fun p => ⟨(ψ p.val.1, ψ p.val.2), by rw [hψ]; exact p.property.1, by
    rw [hψ]; exact p.property.2⟩

/-- The induced map on stage-2 target pairs. -/
def bmap : Bows A dA → Bows B dB :=
  Sum.map (ratmap ψ hψ) (fun y => (cmap ψ hψ y.1, y.2.1, y.2.2))

theorem bmap_injective (hinj : Function.Injective ψ) :
    Function.Injective (bmap ψ hψ) := by
  refine Function.Injective.sumMap ?_ ?_
  · intro p q h
    have h1 : ψ p.val.1 = ψ q.val.1 := congrArg (fun r => (r : RatPairs B dB).val.1) h
    have h2 : ψ p.val.2 = ψ q.val.2 := congrArg (fun r => (r : RatPairs B dB).val.2) h
    exact Subtype.ext (Prod.ext (hinj h1) (hinj h2))
  · intro y y' h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (cmap_injective ψ hψ hinj h.1) (Prod.ext h.2.1 h.2.2)

theorem banc_transport (j : Bows A dA) (l : Bool) :
    banc dB (bmap ψ hψ j) l = w1map ψ hψ (banc dA j l) := by
  match j, l with
  | Sum.inl p, false => rfl
  | Sum.inl p, true => rfl
  | Sum.inr (p, n, o), l =>
      show chp dB (cmap ψ hψ p) _ = w1map ψ hψ (chp dA p _)
      rw [w1map_chp]

/-- **The canonical extension of a distance-preserving injection.** -/
noncomputable def EMap (hinj : Function.Injective ψ) : ECarrier A dA → ECarrier B dB :=
  Sum.map (w1map ψ hψ)
    (Stage2.decorMap (dist1_transport ψ hψ hinj) (banc_transport ψ hψ))

theorem EMap_einl (hinj : Function.Injective ψ) (a : A) :
    EMap ψ hψ hinj (einl dA a) = einl dB (ψ a) := rfl

/-- **`E(ψ)` is distance preserving.** -/
theorem EMap_iso (hinj : Function.Injective ψ) (x y : ECarrier A dA) :
    EDist dB (EMap ψ hψ hinj x) (EMap ψ hψ hinj y) = EDist dA x y :=
  Stage2.frzDist_transport (dist1_transport ψ hψ hinj) (banc_transport ψ hψ)
    (bmap_injective ψ hψ hinj) x y

theorem EMap_injective (hinj : Function.Injective ψ) :
    Function.Injective (EMap ψ hψ hinj) := by
  refine Function.Injective.sumMap (w1map_injective ψ hψ hinj) ?_
  intro z z' h
  have h1 := congrArg Subtype.val h
  simp only [Stage2.decorMap_val, Prod.mk.injEq] at h1
  exact Subtype.ext (Prod.ext (bmap_injective ψ hψ hinj h1.1) h1.2)

end

/-! ### Composition, identity, surjectivity -/

section

variable {A B C : Type u} {dA : A → A → ℝ} {dB : B → B → ℝ} {dC : C → C → ℝ}

theorem EMap_congr {ψ ψ' : A → B} (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hψ' : ∀ a a', dB (ψ' a) (ψ' a') = dA a a') (hinj : Function.Injective ψ)
    (hinj' : Function.Injective ψ') (h : ψ = ψ') (x : ECarrier A dA) :
    EMap ψ hψ hinj x = EMap ψ' hψ' hinj' x := by
  subst h; rfl

theorem EMap_id (h : ∀ a a', dA a a' = dA a a') (hinj : Function.Injective (id : A → A))
    (x : ECarrier A dA) : EMap id h hinj x = x := by
  rcases x with (w | z)
  · rcases w with (a | ⟨p, n⟩) <;> rfl
  · obtain ⟨⟨j, n, s⟩, h1, h2⟩ := z
    cases j <;> rfl

/-- **`E` preserves composition.** -/
theorem EMap_comp {ψ : A → B} {χ : B → C}
    (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hχ : ∀ b b', dC (χ b) (χ b') = dB b b')
    (hinjψ : Function.Injective ψ) (hinjχ : Function.Injective χ)
    (hcomp : ∀ a a', dC ((χ ∘ ψ) a) ((χ ∘ ψ) a') = dA a a')
    (hinjc : Function.Injective (χ ∘ ψ)) (x : ECarrier A dA) :
    EMap χ hχ hinjχ (EMap ψ hψ hinjψ x) = EMap (χ ∘ ψ) hcomp hinjc x := by
  rcases x with (w | z)
  · rcases w with (a | ⟨p, n⟩) <;> rfl
  · obtain ⟨⟨j, n, s⟩, h1, h2⟩ := z
    cases j <;> rfl

/-- **`E` preserves surjectivity.** -/
theorem EMap_surjective {ψ : A → B} (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hbij : Function.Bijective ψ) :
    Function.Surjective (EMap ψ hψ hbij.1) := by
  obtain ⟨σ, hσ1, hσ2⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hσ : ∀ b b', dA (σ b) (σ b') = dB b b' := by
    intro b b'
    have := hψ (σ b) (σ b')
    rw [hσ2 b, hσ2 b'] at this
    exact this.symm
  have hinjσ : Function.Injective σ := Function.LeftInverse.injective hσ2
  have hps : ψ ∘ σ = id := funext hσ2
  have hcomp : ∀ b b', dB ((ψ ∘ σ) b) ((ψ ∘ σ) b') = dB b b' := by
    intro b b'
    simp only [Function.comp_apply, hψ, hσ]
  have hinjc : Function.Injective (ψ ∘ σ) := hbij.1.comp hinjσ
  intro x
  refine ⟨EMap σ hσ hinjσ x, ?_⟩
  rw [EMap_comp hσ hψ hinjσ hbij.1 hcomp hinjc x]
  rw [EMap_congr hcomp (fun b b' => rfl) hinjc Function.injective_id hps x]
  exact EMap_id (fun b b' => rfl) Function.injective_id x

end

/-! ### The commission's shapes -/

section

variable {A B : Type u} {dA : A → A → ℝ} {dB : B → B → ℝ}

/-- **Functoriality of the canonical extension** (paper Theorem 6.3): a distance-preserving
injection of the cores induces a distance-preserving injection of the extensions,
commuting with the inclusions. -/
theorem E_functor (ψ : A → B) (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hinj : Function.Injective ψ) :
    ∃ Ψ : ECarrier A dA → ECarrier B dB,
      Function.Injective Ψ ∧ (∀ a, Ψ (einl dA a) = einl dB (ψ a)) ∧
        ∀ x y, EDist dB (Ψ x) (Ψ y) = EDist dA x y :=
  ⟨EMap ψ hψ hinj, EMap_injective ψ hψ hinj, EMap_einl ψ hψ hinj, EMap_iso ψ hψ hinj⟩

/-- **`E` of a surjection is surjective**: a distance-preserving bijection of the cores
induces a distance-preserving bijection of the extensions. -/
theorem E_functor_surj (ψ : A → B) (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hbij : Function.Bijective ψ) :
    ∃ Ψ : ECarrier A dA → ECarrier B dB,
      Function.Bijective Ψ ∧ (∀ a, Ψ (einl dA a) = einl dB (ψ a)) ∧
        ∀ x y, EDist dB (Ψ x) (Ψ y) = EDist dA x y :=
  ⟨EMap ψ hψ hbij.1, ⟨EMap_injective ψ hψ hbij.1, EMap_surjective hψ hbij⟩,
    EMap_einl ψ hψ hbij.1, EMap_iso ψ hψ hbij.1⟩

/-- **`E` preserves composition** (the commission's shape). -/
theorem E_functor_comp {C : Type u} {dC : C → C → ℝ} (ψ : A → B) (χ : B → C)
    (hψ : ∀ a a', dB (ψ a) (ψ a') = dA a a')
    (hχ : ∀ b b', dC (χ b) (χ b') = dB b b')
    (hinjψ : Function.Injective ψ) (hinjχ : Function.Injective χ) :
    ∃ (hcomp : ∀ a a', dC ((χ ∘ ψ) a) ((χ ∘ ψ) a') = dA a a')
      (hinjc : Function.Injective (χ ∘ ψ)),
      ∀ x, EMap χ hχ hinjχ (EMap ψ hψ hinjψ x) = EMap (χ ∘ ψ) hcomp hinjc x := by
  refine ⟨fun a a' => by simp only [Function.comp_apply, hχ, hψ], hinjχ.comp hinjψ, ?_⟩
  intro x
  exact EMap_comp hψ hχ hinjψ hinjχ _ _ x

end

end Canonical
