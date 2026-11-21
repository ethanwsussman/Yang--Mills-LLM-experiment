import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsOfTheChartEnergyProof
import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeftLogarithmOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages
namespace ChartSecondDeriv
section Calculus
variable {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
theorem fderiv_fderiv_comp_apply {Φ : Q → R} {T : P → Q} {x : P} (hΦ : ContDiffAt ℝ 3 Φ (T x))
    (hT : ContDiffAt ℝ 3 T x) (u v : P) :
    fderiv ℝ (fun ζ => fderiv ℝ (Φ ∘ T) ζ u) x v =
      fderiv ℝ (fderiv ℝ Φ) (T x) (fderiv ℝ T x v) (fderiv ℝ T x u) +
        fderiv ℝ Φ (T x) (fderiv ℝ (fun ζ => fderiv ℝ T ζ u) x v) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.fderiv_fderiv_comp_apply <;> assumption
theorem fderiv_fderiv_comp_clm {Φ : Q → R} (l : P →L[ℝ] Q) {x : P} (hΦ : ContDiffAt ℝ 3 Φ (l x))
    (u v : P) :
    fderiv ℝ (fderiv ℝ (Φ ∘ l)) x v u = fderiv ℝ (fderiv ℝ Φ) (l x) (l v) (l u) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.fderiv_fderiv_comp_clm <;> assumption
end Calculus
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
theorem norm_toImaginaryCLM (v : BondVector) : ‖toImaginaryCLM v‖ = ‖v‖ := by
  have h1 : ‖toImaginaryCLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h := Quaternion.normSq_eq_norm_mul_self ((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])
    rw [Quaternion.normSq_def'] at h
    have h2 : ‖(toImaginaryCLM v : imaginaryQuaternions)‖ =
        ‖((toImaginaryCLM v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
    rw [h2, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
    simp only [toImaginaryCLM_apply, toImaginary, Real.norm_eq_abs, sq_abs] at h ⊢
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
open Classical in
def extendByZero (p : ChordBond F → imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun y i => if h : (y, i) ∈ chordBonds (finiteCells F) then p ⟨(y, i), h⟩ else 0
theorem expUnit_at_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
def rotateGaugeBy (W : F.GaugeField F.depth) (p : ChordBond F → imaginaryQuaternions) :
    F.GaugeField F.depth :=
  leftTranslate (extendByZero p) W
section Spread
def imagBasis : Module.Basis (Fin (Module.finrank ℝ imaginaryQuaternions)) ℝ imaginaryQuaternions :=
  Module.finBasis ℝ imaginaryQuaternions
abbrev BondBasisPair (F : BlockFrame) : Type :=
  ChordBond F × Fin (Module.finrank ℝ imaginaryQuaternions)
def pairEquiv (F : BlockFrame) : BondBasisPair F ≃ Fin (Fintype.card (BondBasisPair F)) :=
  Fintype.equivFin _
def pairBond (F : BlockFrame) : Fin (Fintype.card (BondBasisPair F)) → F.Site F.depth × Fin 4 :=
  fun l => ((pairEquiv F).symm l).1.1
def pairDir (F : BlockFrame) : Fin (Fintype.card (BondBasisPair F)) → imaginaryQuaternions :=
  fun l => imagBasis ((pairEquiv F).symm l).2
def coordsLinear (F : BlockFrame) :
    (ChordBond F → imaginaryQuaternions) →ₗ[ℝ] (Fin (Fintype.card (BondBasisPair F)) → ℝ) :=
  LinearMap.pi fun l =>
    (imagBasis.coord ((pairEquiv F).symm l).2).comp (LinearMap.proj ((pairEquiv F).symm l).1)
def coordsCLM (F : BlockFrame) :
    (ChordBond F → imaginaryQuaternions) →L[ℝ] (Fin (Fintype.card (BondBasisPair F)) → ℝ) :=
  LinearMap.toContinuousLinearMap (coordsLinear F)
theorem bondSpread_coordsCLM (p : ChordBond F → imaginaryQuaternions) (y : F.Site F.depth)
    (i : Fin 4) :
    bondSpread (pairBond F) (pairDir F) (coordsCLM F p) y i = extendByZero p y i := by
  classical
  have h1 : ∑ l, (if pairBond F l = (y, i) then (coordsCLM F p l) • pairDir F l else 0) =
      ∑ q : BondBasisPair F,
        if q.1.1 = (y, i) then (imagBasis.repr (p q.1) q.2) • imagBasis q.2 else 0 := by
    refine Fintype.sum_equiv (pairEquiv F).symm _ _ fun l => ?_
    simp [pairBond, pairDir, coordsCLM, coordsLinear]
  have h2 : ∑ q : BondBasisPair F,
      (if q.1.1 = (y, i) then (imagBasis.repr (p q.1) q.2) • imagBasis q.2 else 0) =
      ∑ b : ChordBond F, if b.1 = (y, i) then p b else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b.1 = (y, i)
    · simp only [hb, if_true]
      exact imagBasis.sum_repr (p b)
    · simp [hb]
  change (∑ l, if pairBond F l = (y, i) then (coordsCLM F p l) • pairDir F l else 0) = _
  rw [h1, h2]
  unfold extendByZero
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(y, i), h⟩ : ChordBond F)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hc
      exact hb (Subtype.ext hc)
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hc
    exact h (hc ▸ b.2)
theorem contDiffAt_comp_rotateBy {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth} (hG : ContDiffThreeAlongBonds G W) :
    ContDiffAt ℝ 3 (fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) 0 := by
  have h0 := hG _ (pairBond F) (pairDir F)
  have hc : ContDiffAt ℝ 3 (coordsCLM F) (0 : ChordBond F → imaginaryQuaternions) :=
    (coordsCLM F).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ 3 (fun τ : Fin (Fintype.card (BondBasisPair F)) → ℝ =>
      G (leftTranslate (bondSpread (pairBond F) (pairDir F) τ) W)) (coordsCLM F 0) := by
    simpa using h0
  have h2 := h1.comp (0 : ChordBond F → imaginaryQuaternions) hc
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  have : bondSpread (pairBond F) (pairDir F) (coordsCLM F p) = extendByZero p := by
    funext y i
    exact bondSpread_coordsCLM p y i
  simp only [Function.comp, this, rotateGaugeBy]
end Spread
theorem bondSpread_single (b : ChordBond F) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ) :
    bondSpread ![b.1] ![X] τ = extendByZero (Pi.single b (τ 0 • X)) := by
  funext y i
  simp only [bondSpread, extendByZero, Fin.sum_univ_one]
  by_cases h : (y, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : b.1 = (y, i)
    · have : (⟨(y, i), h⟩ : ChordBond F) = b := Subtype.ext hb.symm
      simp [this, hb]
    · have : (⟨(y, i), h⟩ : ChordBond F) ≠ b := fun hc => hb (congrArg Subtype.val hc).symm
      simp [hb, Pi.single_eq_of_ne this]
  · rw [dif_neg h]
    have hb : b.1 ≠ (y, i) := fun hc => h (hc ▸ b.2)
    simp [hb]
theorem bondSpread_pair (b b' : ChordBond F) (X X' : imaginaryQuaternions) (τ : Fin 2 → ℝ) :
    bondSpread ![b.1, b'.1] ![X, X'] τ =
      extendByZero (Pi.single b (τ 0 • X) + Pi.single b' (τ 1 • X')) := by
  funext y i
  simp only [bondSpread, extendByZero, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h : (y, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h, Pi.add_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · by_cases hb : b.1 = (y, i)
      · have : (⟨(y, i), h⟩ : ChordBond F) = b := Subtype.ext hb.symm
        simp [this, hb]
      · have : (⟨(y, i), h⟩ : ChordBond F) ≠ b := fun hc => hb (congrArg Subtype.val hc).symm
        simp [hb, Pi.single_eq_of_ne this]
    · by_cases hb : b'.1 = (y, i)
      · have : (⟨(y, i), h⟩ : ChordBond F) = b' := Subtype.ext hb.symm
        simp [this, hb]
      · have : (⟨(y, i), h⟩ : ChordBond F) ≠ b' := fun hc => hb (congrArg Subtype.val hc).symm
        simp [hb, Pi.single_eq_of_ne this]
  · rw [dif_neg h]
    have hb : b.1 ≠ (y, i) := fun hc => h (hc ▸ b.2)
    have hb' : b'.1 ≠ (y, i) := fun hc => h (hc ▸ b'.2)
    simp [hb, hb']
def singleLine (b : ChordBond F) (X : imaginaryQuaternions) :
    (Fin 1 → ℝ) →L[ℝ] (ChordBond F → imaginaryQuaternions) :=
  ((ContinuousLinearMap.proj (0 : Fin 1)).smulRight
    (Pi.single b X : ChordBond F → imaginaryQuaternions))
def pairPlane (b b' : ChordBond F) (X X' : imaginaryQuaternions) :
    (Fin 2 → ℝ) →L[ℝ] (ChordBond F → imaginaryQuaternions) :=
  ((ContinuousLinearMap.proj (0 : Fin 2)).smulRight
    (Pi.single b X : ChordBond F → imaginaryQuaternions)) +
    ((ContinuousLinearMap.proj (1 : Fin 2)).smulRight
      (Pi.single b' X' : ChordBond F → imaginaryQuaternions))
theorem singleLine_apply (b : ChordBond F) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ) :
    singleLine b X τ = Pi.single b (τ 0 • X) := by
  funext d
  by_cases h : d = b
  · subst h
    simp [singleLine]
  · simp [singleLine, Pi.single_eq_of_ne h]
theorem pairPlane_apply (b b' : ChordBond F) (X X' : imaginaryQuaternions) (τ : Fin 2 → ℝ) :
    pairPlane b b' X X' τ = Pi.single b (τ 0 • X) + Pi.single b' (τ 1 • X') := by
  funext d
  have h1 : ∀ (c : ChordBond F) (Z : imaginaryQuaternions) (r : ℝ),
      r • (Pi.single c Z : ChordBond F → imaginaryQuaternions) d =
      (Pi.single c (r • Z) : ChordBond F → imaginaryQuaternions) d := by
    intro c Z r
    by_cases h : d = c
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  simp [pairPlane, h1]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem bondDeriv_single_eq {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) (b : ChordBond F) (X : imaginaryQuaternions) :
    bondDeriv G W ![b.1] ![X] =
      fderiv ℝ (fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) 0
        (Pi.single b X) := by
  have hΦ := contDiffAt_comp_rotateBy hG
  have hf : (fun τ : Fin 1 → ℝ => G (leftTranslate (bondSpread ![b.1] ![X] τ) W)) =
      (fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) ∘ singleLine b X := by
    funext τ
    simp only [Function.comp, rotateGaugeBy, singleLine_apply, bondSpread_single]
  unfold bondDeriv
  rw [hf, iteratedFDeriv_one_apply]
  have d : DifferentiableAt ℝ (fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p))
      (singleLine b X 0) := by
    simpa using hΦ.differentiableAt (by norm_num)
  rw [fderiv_comp _ d (singleLine b X).differentiableAt, (singleLine b X).fderiv]
  simp [singleLine_apply]
theorem bondDeriv_pair_eq {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) (b b' : ChordBond F) (X X' : imaginaryQuaternions) :
    bondDeriv G W ![b.1, b'.1] ![X, X'] =
      fderiv ℝ (fderiv ℝ fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) 0
        (Pi.single b X) (Pi.single b' X') := by
  have hΦ := contDiffAt_comp_rotateBy hG
  have hf : (fun τ : Fin 2 → ℝ => G (leftTranslate (bondSpread ![b.1, b'.1] ![X, X'] τ) W)) =
      (fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) ∘ pairPlane b b' X X' := by
    funext τ
    simp only [Function.comp, rotateGaugeBy, pairPlane_apply, bondSpread_pair]
  unfold bondDeriv
  rw [hf, iteratedFDeriv_two_apply]
  have h0 : pairPlane b b' X X' 0 = 0 := map_zero _
  have := fderiv_fderiv_comp_clm
    (Φ := fun p : ChordBond F → imaginaryQuaternions => G (rotateGaugeBy W p)) (pairPlane b b' X X')
    (x := 0) (by rw [h0]; exact hΦ) (Pi.single 1 1) (Pi.single 0 1)
  simp only [Function.comp_def] at this ⊢
  rw [this, h0]
  simp [pairPlane_apply]
theorem exists_norm_eq_one : ∃ Z : imaginaryQuaternions, ‖Z‖ = 1 := by
  refine ⟨toImaginaryCLM (EuclideanSpace.single 0 1), ?_⟩
  rw [norm_toImaginaryCLM]
  simp
theorem bondDeriv_single_smul {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) (b : ChordBond F) (X : imaginaryQuaternions) (r : ℝ) :
    bondDeriv G W ![b.1] ![r • X] = r • bondDeriv G W ![b.1] ![X] := by
  rw [bondDeriv_single_eq hG, bondDeriv_single_eq hG, ← map_smul, Pi.single_smul]
theorem bondDeriv_pair_smul {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) (b b' : ChordBond F) (X X' : imaginaryQuaternions)
    (r r' : ℝ) :
    bondDeriv G W ![b.1, b'.1] ![r • X, r' • X'] =
      (r * r') • bondDeriv G W ![b.1, b'.1] ![X, X'] := by
  rw [bondDeriv_pair_eq hG, bondDeriv_pair_eq hG, Pi.single_smul, Pi.single_smul, map_smul,
    map_smul, ContinuousLinearMap.smul_apply, smul_smul, mul_comm]
theorem norm_bondDeriv_single_le {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) {b : ChordBond F} {B : ℝ}
    (h : ∀ Z : imaginaryQuaternions, ‖Z‖ = 1 → ‖bondDeriv G W ![b.1] ![Z]‖ ≤ B)
    (Y : imaginaryQuaternions) :
    ‖bondDeriv G W ![b.1] ![Y]‖ ≤ B * ‖Y‖ := by
  by_cases hY : Y = 0
  · have h0 := bondDeriv_single_smul hG b Y 0
    simp only [zero_smul] at h0
    subst hY
    simp [h0]
  · have hn : ‖Y‖ ≠ 0 := norm_ne_zero_iff.2 hY
    have hu : ‖(‖Y‖⁻¹ • Y : imaginaryQuaternions)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have e : Y = ‖Y‖ • (‖Y‖⁻¹ • Y : imaginaryQuaternions) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h1 := h _ hu
    rw [e, bondDeriv_single_smul hG, norm_smul, ← e, norm_norm]
    nlinarith [norm_nonneg Y]
theorem norm_bondDeriv_pair_le {G : F.GaugeField F.depth → E} {W : F.GaugeField F.depth}
    (hG : ContDiffThreeAlongBonds G W) {b b' : ChordBond F} {B : ℝ}
    (h : ∀ Z Z' : imaginaryQuaternions, ‖Z‖ = 1 → ‖Z'‖ = 1 →
      ‖bondDeriv G W ![b.1, b'.1] ![Z, Z']‖ ≤ B)
    (Y Y' : imaginaryQuaternions) : ‖bondDeriv G W ![b.1, b'.1] ![Y, Y']‖ ≤ B * ‖Y‖ * ‖Y'‖ := by
  have key : ∀ Y Y' : imaginaryQuaternions,
      ‖bondDeriv G W ![b.1, b'.1] ![Y, Y']‖ ≤ B * ‖Y‖ * ‖Y'‖ := by
    intro Y Y'
    by_cases hY : Y = 0
    · have h0 := bondDeriv_pair_smul hG b b' Y Y' 0 1
      simp only [zero_smul, one_smul, zero_mul] at h0
      subst hY
      simp [h0]
    · by_cases hY' : Y' = 0
      · have h0 := bondDeriv_pair_smul hG b b' Y Y' 1 0
        simp only [zero_smul, one_smul, mul_zero] at h0
        subst hY'
        simp [h0]
      · have hn : ‖Y‖ ≠ 0 := norm_ne_zero_iff.2 hY
        have hn' : ‖Y'‖ ≠ 0 := norm_ne_zero_iff.2 hY'
        have hu : ‖(‖Y‖⁻¹ • Y : imaginaryQuaternions)‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have hu' : ‖(‖Y'‖⁻¹ • Y' : imaginaryQuaternions)‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
        have e : Y = ‖Y‖ • (‖Y‖⁻¹ • Y : imaginaryQuaternions) := by
          rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
        have e' : Y' = ‖Y'‖ • (‖Y'‖⁻¹ • Y' : imaginaryQuaternions) := by
          rw [smul_smul, mul_inv_cancel₀ hn', one_smul]
        have h1 := h _ _ hu hu'
        have h2 := bondDeriv_pair_smul hG b b' (‖Y‖⁻¹ • Y) (‖Y'‖⁻¹ • Y') ‖Y‖ ‖Y'‖
        rw [← e, ← e'] at h2
        rw [h2, norm_smul, norm_mul, norm_norm, norm_norm]
        nlinarith [norm_nonneg Y, norm_nonneg Y', mul_nonneg (norm_nonneg Y) (norm_nonneg Y')]
  exact key Y Y'
def logFamily (Θ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F)) : ChordBond F → imaginaryQuaternions :=
  fun b => Θ (w b.1.1 b.1.2, toImaginaryCLM (ζ b))
theorem chartedField_add_eq_rotateBy
    {Θ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {ζ : StepVariable (finiteCells F)}
    (hev : ∀ b : ChordBond F, expUnit (w b.1.1 b.1.2 + toImaginaryCLM (ζ b)) =
      expUnit (Θ (w b.1.1 b.1.2, toImaginaryCLM (ζ b))) * expUnit (w b.1.1 b.1.2)) :
    chartedField (fun x i => w x i + stepCoordinates ζ x i) V =
      rotateGaugeBy (chartedField w V) (logFamily Θ w ζ) := by
  classical
  funext x i
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · have hnt : ¬ IsAxialTreeBond (x, i) := (Finset.mem_filter.1 h).2
    have hb : expUnit (w x i + toImaginaryCLM (ζ ⟨(x, i), h⟩)) =
        expUnit (Θ (w x i, toImaginaryCLM (ζ ⟨(x, i), h⟩))) * expUnit (w x i) :=
      hev ⟨(x, i), h⟩
    have hc : stepCoordinates ζ x i = toImaginaryCLM (ζ ⟨(x, i), h⟩) := by
      simp [stepCoordinates, h, toImaginaryCLM_apply]
    have he : extendByZero (logFamily Θ w ζ) x i = Θ (w x i, toImaginaryCLM (ζ ⟨(x, i), h⟩)) := by
      simp [extendByZero, h, logFamily]
    simp only [rotateGaugeBy, leftTranslate, he]
    simp only [chartedField, hc]
    by_cases hcr : IsCrossingBond (x, i)
    · simp only [hcr, if_true]
      rw [← mul_assoc, ← hb]
    · simp only [hcr, if_false, hnt]
      exact hb
  · have hc : stepCoordinates ζ x i = 0 := by simp [stepCoordinates, h]
    have he : extendByZero (logFamily Θ w ζ) x i = 0 := by simp [extendByZero, h]
    simp only [rotateGaugeBy, leftTranslate, he, expUnit_at_zero, one_mul]
    simp only [chartedField, hc, add_zero]
section Derivatives
variable {τ : F.Site F.depth → Fin 4 → imaginaryQuaternions → imaginaryQuaternions}
def bondwiseFamily (τ : F.Site F.depth → Fin 4 → imaginaryQuaternions → imaginaryQuaternions)
    (ζ : StepVariable (finiteCells F)) : ChordBond F → imaginaryQuaternions :=
  fun b => τ b.1.1 b.1.2 (toImaginaryCLM (ζ b))
theorem contDiffAt_bondwiseFamily (h : ∀ b : ChordBond F, ContDiffAt ℝ 3 (τ b.1.1 b.1.2) 0) :
    ContDiffAt ℝ 3 (bondwiseFamily τ) (0 : StepVariable (finiteCells F)) := by
  rw [contDiffAt_pi]
  intro b
  have h1 : ContDiffAt ℝ 3 (τ b.1.1 b.1.2)
      (toImaginaryCLM ((0 : StepVariable (finiteCells F)) b)) := by
    simpa using h b
  have h2 : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) => toImaginaryCLM (ζ b))
      (0 : StepVariable (finiteCells F)) :=
    (toImaginaryCLM.contDiff.comp (contDiff_apply ℝ BondVector b)).contDiffAt
  exact h1.comp (0 : StepVariable (finiteCells F)) h2
theorem hasFDerivAt_bondwiseFamily {ζ : StepVariable (finiteCells F)}
    (h : ∀ b : ChordBond F, DifferentiableAt ℝ (τ b.1.1 b.1.2) (toImaginaryCLM (ζ b))) :
    HasFDerivAt (bondwiseFamily τ) (ContinuousLinearMap.pi fun b : ChordBond F =>
      (fderiv ℝ (τ b.1.1 b.1.2) (toImaginaryCLM (ζ b))).comp
        (toImaginaryCLM.comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) b))) ζ := by
  rw [hasFDerivAt_pi']
  intro b
  have h1 : HasFDerivAt (fun ξ : StepVariable (finiteCells F) => toImaginaryCLM (ξ b))
      (toImaginaryCLM.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) b)) ζ :=
    (toImaginaryCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) b)).hasFDerivAt
  have h2 := (h b).hasFDerivAt.comp ζ h1
  simp only [ContinuousLinearMap.proj_pi]
  exact h2
theorem fderiv_bondwiseFamily {ζ : StepVariable (finiteCells F)}
    (h : ∀ b : ChordBond F, DifferentiableAt ℝ (τ b.1.1 b.1.2) (toImaginaryCLM (ζ b)))
    (u : StepVariable (finiteCells F)) :
    fderiv ℝ (bondwiseFamily τ) ζ u =
      fun b => fderiv ℝ (τ b.1.1 b.1.2) (toImaginaryCLM (ζ b)) (toImaginaryCLM (u b)) := by
  rw [(hasFDerivAt_bondwiseFamily h).fderiv]
  rfl
theorem fderiv_bondwiseFamily_bondVariation
    (h : ∀ b : ChordBond F, ContDiffAt ℝ 3 (τ b.1.1 b.1.2) 0) (b : ChordBond F) (e : BondVector) :
    fderiv ℝ (bondwiseFamily τ) (0 : StepVariable (finiteCells F)) (bondVariation b e) =
      Pi.single b (fderiv ℝ (τ b.1.1 b.1.2) 0 (toImaginaryCLM e)) := by
  have hd : ∀ b : ChordBond F, DifferentiableAt ℝ (τ b.1.1 b.1.2)
      (toImaginaryCLM ((0 : StepVariable (finiteCells F)) b)) := fun b => by
    simpa using (h b).differentiableAt (by norm_num)
  rw [fderiv_bondwiseFamily hd]
  funext d
  by_cases hdb : d = b
  · subst hdb
    simp [bondVariation]
  · simp [bondVariation, Pi.single_eq_of_ne hdb]
theorem fderiv_fderiv_bondwiseFamily_bondVariation
    (h : ∀ b : ChordBond F, ContDiffAt ℝ 3 (τ b.1.1 b.1.2) 0) (b b' : ChordBond F)
    (e e' : BondVector) :
    fderiv ℝ (fun ζ => fderiv ℝ (bondwiseFamily τ) ζ (bondVariation b e))
        (0 : StepVariable (finiteCells F)) (bondVariation b' e') =
      if b = b' then
        Pi.single b (fderiv ℝ (fun z => fderiv ℝ (τ b.1.1 b.1.2) z (toImaginaryCLM e)) 0
          (toImaginaryCLM e'))
      else 0 := by
  have hev : ∀ᶠ ζ in 𝓝 (0 : StepVariable (finiteCells F)), ∀ d : ChordBond F,
      DifferentiableAt ℝ (τ d.1.1 d.1.2) (toImaginaryCLM (ζ d)) := by
    rw [Filter.eventually_all]
    intro d
    have hc : ContinuousAt (fun ζ : StepVariable (finiteCells F) => toImaginaryCLM (ζ d)) 0 :=
      (toImaginaryCLM.continuous.comp (continuous_apply d)).continuousAt
    have h0 : ∀ᶠ z in 𝓝 (toImaginaryCLM ((0 : StepVariable (finiteCells F)) d)),
        DifferentiableAt ℝ (τ d.1.1 d.1.2) z := by
      have : ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions), ContDiffAt ℝ 3 (τ d.1.1 d.1.2) z :=
        (h d).eventually (by simp)
      simp only [Pi.zero_apply, map_zero]
      filter_upwards [this] with z hz using hz.differentiableAt (by norm_num)
    exact hc.eventually h0
  have he : (fun ζ => fderiv ℝ (bondwiseFamily τ) ζ (bondVariation b e)) =ᶠ[𝓝 (0 : StepVariable (finiteCells F))]
      fun ζ d => fderiv ℝ (τ d.1.1 d.1.2) (toImaginaryCLM (ζ d))
        (toImaginaryCLM (bondVariation b e d)) := by
    filter_upwards [hev] with ζ hζ
    exact fderiv_bondwiseFamily hζ _
  rw [he.fderiv_eq]
  have hdiff : ∀ (d : ChordBond F) (l : imaginaryQuaternions),
      DifferentiableAt ℝ (fun z => fderiv ℝ (τ d.1.1 d.1.2) z l) 0 := by
    intro d l
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ (τ d.1.1 d.1.2)) 0 := (h d).fderiv_right (by norm_num)
    exact (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const l)
  have hpi : HasFDerivAt (fun (ζ : StepVariable (finiteCells F)) (d : ChordBond F) =>
      fderiv ℝ (τ d.1.1 d.1.2) (toImaginaryCLM (ζ d)) (toImaginaryCLM (bondVariation b e d)))
      (ContinuousLinearMap.pi fun d : ChordBond F =>
        (fderiv ℝ (fun z => fderiv ℝ (τ d.1.1 d.1.2) z (toImaginaryCLM (bondVariation b e d))) 0).comp
          (toImaginaryCLM.comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) d))) 0 := by
    rw [hasFDerivAt_pi']
    intro d
    have h1 : HasFDerivAt (fun ξ : StepVariable (finiteCells F) => toImaginaryCLM (ξ d))
        (toImaginaryCLM.comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) d)) 0 :=
      (toImaginaryCLM.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChordBond F => BondVector) d)).hasFDerivAt
    have h3 : HasFDerivAt (fun z => fderiv ℝ (τ d.1.1 d.1.2) z (toImaginaryCLM (bondVariation b e d)))
        (fderiv ℝ (fun z => fderiv ℝ (τ d.1.1 d.1.2) z (toImaginaryCLM (bondVariation b e d))) 0)
        (toImaginaryCLM ((0 : StepVariable (finiteCells F)) d)) := by
      simpa using (hdiff d (toImaginaryCLM (bondVariation b e d))).hasFDerivAt
    have h2 := h3.comp (0 : StepVariable (finiteCells F)) h1
    simp only [ContinuousLinearMap.proj_pi]
    exact h2
  rw [hpi.fderiv]
  funext d
  change fderiv ℝ (fun z => fderiv ℝ (τ d.1.1 d.1.2) z (toImaginaryCLM (bondVariation b e d))) 0
    (toImaginaryCLM (bondVariation b' e' d)) = _
  by_cases hdb : d = b
  · subst hdb
    by_cases hbb : d = b'
    · subst hbb
      simp [bondVariation]
    · have : (Pi.single b' e' : StepVariable (finiteCells F)) d = 0 := Pi.single_eq_of_ne hbb _
      simp [bondVariation, this, hbb]
  · have h0 : toImaginaryCLM (bondVariation b e d) = 0 := by
      have : (Pi.single b e : StepVariable (finiteCells F)) d = 0 := Pi.single_eq_of_ne hdb _
      simp [bondVariation, this]
    rw [h0]
    have hz : (fun z => fderiv ℝ (τ d.1.1 d.1.2) z (0 : imaginaryQuaternions)) =
        fun _ => (0 : imaginaryQuaternions) := by
      funext z
      simp
    rw [hz]
    by_cases hbb : b = b'
    · simp [hbb, Pi.single_eq_of_ne (by rw [← hbb]; exact hdb : d ≠ b')]
    · simp [hbb]
end Derivatives
theorem norm_fderiv_snd_le
    {Θ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {v : imaginaryQuaternions} {C : ℝ}
    (hc : ContDiffAt ℝ 3 Θ (v, 0)) (h1 : ‖iteratedFDeriv ℝ 1 Θ (v, 0)‖ ≤ C)
    (l : imaginaryQuaternions) :
    ‖fderiv ℝ (fun z => Θ (v, z)) 0 l‖ ≤ C * ‖l‖ := by
  have hd : DifferentiableAt ℝ Θ (v, 0) := hc.differentiableAt (by norm_num)
  have hi : HasFDerivAt (fun z : imaginaryQuaternions => (v, z))
      (ContinuousLinearMap.inr ℝ imaginaryQuaternions imaginaryQuaternions) 0 :=
    (hasFDerivAt_const v (0 : imaginaryQuaternions)).prodMk (hasFDerivAt_id (0 : imaginaryQuaternions))
  have h2 : HasFDerivAt (fun z : imaginaryQuaternions => Θ (v, z)) ((fderiv ℝ Θ (v, 0)).comp
      (ContinuousLinearMap.inr ℝ imaginaryQuaternions imaginaryQuaternions)) 0 :=
    hd.hasFDerivAt.comp (0 : imaginaryQuaternions) hi
  rw [h2.fderiv]
  rw [norm_iteratedFDeriv_one] at h1
  have h3 : ‖(((0 : imaginaryQuaternions), l) : imaginaryQuaternions × imaginaryQuaternions)‖ =
      ‖l‖ := by simp [Prod.norm_def]
  calc ‖((fderiv ℝ Θ (v, 0)).comp
        (ContinuousLinearMap.inr ℝ imaginaryQuaternions imaginaryQuaternions)) l‖
      = ‖fderiv ℝ Θ (v, 0) (0, l)‖ := by simp
    _ ≤ ‖fderiv ℝ Θ (v, 0)‖ *
        ‖(((0 : imaginaryQuaternions), l) : imaginaryQuaternions × imaginaryQuaternions)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖l‖ := by
        rw [h3]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
theorem norm_fderiv_fderiv_snd_le
    {Θ : imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {v : imaginaryQuaternions} {C : ℝ}
    (hc : ContDiffAt ℝ 3 Θ (v, 0)) (h2 : ‖iteratedFDeriv ℝ 2 Θ (v, 0)‖ ≤ C)
    (l l' : imaginaryQuaternions) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun z' => Θ (v, z')) z l) 0 l'‖ ≤ C * ‖l‖ * ‖l'‖ := by
  have hι : ∀ z : imaginaryQuaternions, HasFDerivAt (fun z : imaginaryQuaternions => (v, z))
      (ContinuousLinearMap.inr ℝ imaginaryQuaternions imaginaryQuaternions) z :=
    fun z => (hasFDerivAt_const v z).prodMk (hasFDerivAt_id z)
  have hιc : ContDiffAt ℝ 3 (fun z : imaginaryQuaternions => (v, z)) 0 :=
    (contDiff_const.prodMk contDiff_id).contDiffAt
  have key := fderiv_fderiv_comp_apply (Φ := Θ) (T := fun z : imaginaryQuaternions => (v, z))
    (x := (0 : imaginaryQuaternions)) hc hιc l l'
  have hz : (fun ζ : imaginaryQuaternions => fderiv ℝ (fun z : imaginaryQuaternions => (v, z)) ζ l) =
      fun _ => (0, l) := by
    funext ζ
    rw [(hι ζ).fderiv]
    simp
  have hf0 : fderiv ℝ (fun z : imaginaryQuaternions => (v, z)) 0 =
      ContinuousLinearMap.inr ℝ imaginaryQuaternions imaginaryQuaternions := (hι 0).fderiv
  simp only [Function.comp_def] at key
  rw [key, hz, hf0]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero, add_zero,
    ContinuousLinearMap.inr_apply]
  have n1 : ‖(((0 : imaginaryQuaternions), l) : imaginaryQuaternions × imaginaryQuaternions)‖ =
      ‖l‖ := by simp [Prod.norm_def]
  have n2 : ‖(((0 : imaginaryQuaternions), l') : imaginaryQuaternions × imaginaryQuaternions)‖ =
      ‖l'‖ := by simp [Prod.norm_def]
  have hm : iteratedFDeriv ℝ 2 Θ (v, 0)
      ![((0 : imaginaryQuaternions), l'), ((0 : imaginaryQuaternions), l)] =
      fderiv ℝ (fderiv ℝ Θ) (v, 0) ((0 : imaginaryQuaternions), l')
        ((0 : imaginaryQuaternions), l) := by
    rw [iteratedFDeriv_two_apply]
    simp
  rw [← hm]
  have h3 := (iteratedFDeriv ℝ 2 Θ (v, 0)).le_opNorm
    ![((0 : imaginaryQuaternions), l'), ((0 : imaginaryQuaternions), l)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, n1, n2] at h3
  have nl := norm_nonneg l
  have nl' := norm_nonneg l'
  calc _ ≤ ‖iteratedFDeriv ℝ 2 Θ (v, 0)‖ * (‖l'‖ * ‖l‖) := h3
    _ ≤ C * (‖l'‖ * ‖l‖) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * ‖l‖ * ‖l'‖ := by ring
theorem chartSecondDerivBound_of_leftLogarithmExists (hlog : LeftLogarithmExists) :
    ChartSecondDerivBound := by
  obtain ⟨Θ, C, hC, hsm, hz, hev, hbd⟩ := hlog
  refine ⟨C, hC, ?_⟩
  intro F V w E _ _ G hw hG
  set W : F.GaugeField F.depth := chartedField w V with hW
  set τ : F.Site F.depth → Fin 4 → imaginaryQuaternions → imaginaryQuaternions :=
    fun x i z => Θ (w x i, z) with hτ
  have hsm3 : ∀ v : imaginaryQuaternions, ContDiffAt ℝ 3 Θ (v, 0) :=
    fun v => (hsm v).of_le (by norm_cast <;> exact le_top)
  have hτc : ∀ b : ChordBond F, ContDiffAt ℝ 3 (τ b.1.1 b.1.2) 0 := by
    intro b
    have h2 : ContDiffAt ℝ 3 (fun z : imaginaryQuaternions => (w b.1.1 b.1.2, z)) 0 :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    exact ContDiffAt.comp (0 : imaginaryQuaternions) (hsm3 _) h2
  set Φ : (ChordBond F → imaginaryQuaternions) → E := fun p => G (rotateGaugeBy W p) with hΦd
  have hΦ : ContDiffAt ℝ 3 Φ 0 := contDiffAt_comp_rotateBy hG
  have hT0 : bondwiseFamily τ (0 : StepVariable (finiteCells F)) = 0 := by
    funext b
    simp [bondwiseFamily, hτ, hz]
  have hΦ' : ContDiffAt ℝ 3 Φ (bondwiseFamily τ (0 : StepVariable (finiteCells F))) := by
    rwa [hT0]
  have hT : ContDiffAt ℝ 3 (bondwiseFamily τ) (0 : StepVariable (finiteCells F)) :=
    contDiffAt_bondwiseFamily hτc
  have hevζ : ∀ᶠ ζ in 𝓝 (0 : StepVariable (finiteCells F)), ∀ b : ChordBond F,
      expUnit (w b.1.1 b.1.2 + toImaginaryCLM (ζ b)) =
        expUnit (Θ (w b.1.1 b.1.2, toImaginaryCLM (ζ b))) * expUnit (w b.1.1 b.1.2) := by
    rw [Filter.eventually_all]
    intro b
    have hc : ContinuousAt (fun ζ : StepVariable (finiteCells F) => toImaginaryCLM (ζ b)) 0 :=
      (toImaginaryCLM.continuous.comp (continuous_apply b)).continuousAt
    have h0 : ∀ᶠ z in 𝓝 (toImaginaryCLM ((0 : StepVariable (finiteCells F)) b)),
        expUnit (w b.1.1 b.1.2 + z) = expUnit (Θ (w b.1.1 b.1.2, z)) * expUnit (w b.1.1 b.1.2) := by
      simp only [Pi.zero_apply, map_zero]
      exact hev _
    exact hc.eventually h0
  have hH : readInChart G w V =ᶠ[𝓝 (0 : StepVariable (finiteCells F))] Φ ∘ bondwiseFamily τ := by
    filter_upwards [hevζ] with ζ hζ
    have := chartedField_add_eq_rotateBy (V := V) hζ
    simp only [readInChart, Function.comp, hΦd, this]
    rfl
  have hcomp : ContDiffAt ℝ 3 (Φ ∘ bondwiseFamily τ) (0 : StepVariable (finiteCells F)) :=
    ContDiffAt.comp (0 : StepVariable (finiteCells F)) hΦ' hT
  have hform : ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      ∃ X X' Q : imaginaryQuaternions, ‖X‖ ≤ C * ‖e‖ ∧ ‖X'‖ ≤ C * ‖e'‖ ∧ ‖Q‖ ≤ C * ‖e‖ * ‖e'‖ ∧
        fderiv ℝ (readInChart G w V) 0 (bondVariation b e) =
          bondDeriv G (chartedField w V) ![b.1] ![X] ∧
        fderiv ℝ (fun ζ => fderiv ℝ (readInChart G w V) ζ (bondVariation b e)) 0
            (bondVariation b' e') =
          bondDeriv G (chartedField w V) ![b'.1, b.1] ![X', X] +
            if b = b' then bondDeriv G (chartedField w V) ![b.1] ![Q] else 0 := by
   intro b b' e e'
   refine ⟨fderiv ℝ (τ b.1.1 b.1.2) 0 (toImaginaryCLM e),
    fderiv ℝ (τ b'.1.1 b'.1.2) 0 (toImaginaryCLM e'),
    fderiv ℝ (fun z => fderiv ℝ (τ b.1.1 b.1.2) z (toImaginaryCLM e)) 0 (toImaginaryCLM e'),
    ?_, ?_, ?_, ?_, ?_⟩
   · have := norm_fderiv_snd_le (hsm3 (w b.1.1 b.1.2)) (hbd _ 1 (hw _ b.2) (by norm_num))
       (toImaginaryCLM e)
     rwa [norm_toImaginaryCLM] at this
   · have := norm_fderiv_snd_le (hsm3 (w b'.1.1 b'.1.2)) (hbd _ 1 (hw _ b'.2) (by norm_num))
       (toImaginaryCLM e')
     rwa [norm_toImaginaryCLM] at this
   · have := norm_fderiv_fderiv_snd_le (hsm3 (w b.1.1 b.1.2)) (hbd _ 2 (hw _ b.2) (by norm_num))
       (toImaginaryCLM e) (toImaginaryCLM e')
     rwa [norm_toImaginaryCLM, norm_toImaginaryCLM] at this
   · have hd1 : DifferentiableAt ℝ Φ (bondwiseFamily τ (0 : StepVariable (finiteCells F))) :=
       hΦ'.differentiableAt (by norm_num)
     have hd2 : DifferentiableAt ℝ (bondwiseFamily τ) (0 : StepVariable (finiteCells F)) :=
       hT.differentiableAt (by norm_num)
     rw [hH.fderiv_eq, fderiv_comp _ hd1 hd2, bondDeriv_single_eq hG b]
     simp only [ContinuousLinearMap.comp_apply, fderiv_bondwiseFamily_bondVariation hτc, hT0]
     rfl
   · have he : (fun ζ => fderiv ℝ (readInChart G w V) ζ (bondVariation b e)) =ᶠ[𝓝 (0 : StepVariable (finiteCells F))]
         fun ζ => fderiv ℝ (Φ ∘ bondwiseFamily τ) ζ (bondVariation b e) := by
       filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) hH] with ζ hζ
       rw [hζ]
     rw [he.fderiv_eq, fderiv_fderiv_comp_apply hΦ' hT, fderiv_bondwiseFamily_bondVariation hτc,
       fderiv_bondwiseFamily_bondVariation hτc, fderiv_fderiv_bondwiseFamily_bondVariation hτc, hT0]
     rw [bondDeriv_pair_eq hG b' b]
     congr 1
     by_cases hbb : b = b'
     · simp only [hbb, if_true]
       rw [bondDeriv_single_eq hG b']
     · simp [hbb]
  refine ⟨hcomp.congr_of_eventuallyEq hH, hform, ?_⟩
  intro B₁ B₂ h1 h2 b b' e e'
  obtain ⟨X, X', Q, hX, hX', hQ, he1, he2⟩ := hform b b' e e'
  have hs1 : ∀ (d : ChordBond F) (Y : imaginaryQuaternions),
      ‖bondDeriv G (chartedField w V) ![d.1] ![Y]‖ ≤ B₁ d * ‖Y‖ :=
    fun d Y => norm_bondDeriv_single_le hG (fun Z hZ => h1 d Z hZ) Y
  have hs2 : ‖bondDeriv G (chartedField w V) ![b'.1, b.1] ![X', X]‖ ≤ B₂ b' b * ‖X'‖ * ‖X‖ :=
    norm_bondDeriv_pair_le hG (fun Z Z' hZ hZ' => by simpa using h2 b b' Z' Z hZ' hZ) X' X
  have hB1 : ∀ d : ChordBond F, 0 ≤ B₁ d := fun d => by
    obtain ⟨Z, hZ⟩ := exists_norm_eq_one
    exact (norm_nonneg _).trans (h1 d Z hZ)
  have hB2 : 0 ≤ B₂ b' b := by
    obtain ⟨Z, hZ⟩ := exists_norm_eq_one
    exact (norm_nonneg _).trans (h2 b b' Z Z hZ hZ)
  have ne := norm_nonneg e
  have ne' := norm_nonneg e'
  refine ⟨?_, ?_⟩
  · rw [he1]
    calc _ ≤ B₁ b * ‖X‖ := hs1 b X
      _ ≤ B₁ b * (C * ‖e‖) := mul_le_mul_of_nonneg_left hX (hB1 b)
      _ = _ := by ring
  · rw [he2]
    have hA : ‖bondDeriv G (chartedField w V) ![b'.1, b.1] ![X', X]‖ ≤
        C ^ 2 * B₂ b' b * ‖e‖ * ‖e'‖ := by
      calc _ ≤ B₂ b' b * ‖X'‖ * ‖X‖ := hs2
        _ ≤ B₂ b' b * (C * ‖e'‖) * (C * ‖e‖) := by gcongr
        _ = _ := by ring
    by_cases hbb : b = b'
    · simp only [hbb, if_true] at *
      have hQ2 : ‖bondDeriv G (chartedField w V) ![b'.1] ![Q]‖ ≤ C * B₁ b' * ‖e‖ * ‖e'‖ := by
        calc _ ≤ B₁ b' * ‖Q‖ := hs1 b' Q
          _ ≤ B₁ b' * (C * ‖e‖ * ‖e'‖) := mul_le_mul_of_nonneg_left hQ (hB1 b')
          _ = _ := by ring
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C ^ 2 * B₂ b' b' * ‖e‖ * ‖e'‖ + C * B₁ b' * ‖e‖ * ‖e'‖ := add_le_add hA hQ2
        _ = _ := by ring
    · simp only [hbb, if_false, add_zero]
      exact hA
end ChartSecondDeriv
end ColdStepAtMirrorFrames
end YangMills.Construction
end
