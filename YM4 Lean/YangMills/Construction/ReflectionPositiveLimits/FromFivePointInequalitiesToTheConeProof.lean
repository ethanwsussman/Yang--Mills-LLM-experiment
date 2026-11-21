import YangMills.Construction.EnergyMomentum.JointSpectralMeasureExistence
import YangMills.Construction.ReflectionPositiveLimits.ConstantOneOfTheSinhAndSineInequality
import YangMills.Construction.ReflectionPositiveLimits.FromFivePointInequalitiesToTheCone
import Mathlib
set_option autoImplicit false
open Filter Set Topology MeasureTheory
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.FivePointCone
open YangMills.Construction.ReflectionPositivity YangMills.Construction.EnergyMomentum
open YangMills.Construction.EuclideanSpectral YangMills.Construction.PeriodicLattice
open YangMills.Construction.ReflectionPositivity.DenseTimeReconstruction
open YangMills.Construction.ReflectionPositivity.FunctionalReconstruction
section Adjoints
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isAdjointPair_one : IsAdjointPair (1 : H →L[ℂ] H) 1 := fun _ _ => rfl
theorem isAdjointPair_add {A A' B B' : H →L[ℂ] H} (hA : IsAdjointPair A A') (hB : IsAdjointPair B B') :
    IsAdjointPair (A + B) (A' + B') := by
  intro x y
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hA x y, hB x y]
theorem isAdjointPair_sub {A A' B B' : H →L[ℂ] H} (hA : IsAdjointPair A A') (hB : IsAdjointPair B B') :
    IsAdjointPair (A - B) (A' - B') := by
  intro x y
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hA x y, hB x y]
theorem isAdjointPair_mul {A A' B B' : H →L[ℂ] H} (hA : IsAdjointPair A A') (hB : IsAdjointPair B B') :
    IsAdjointPair (A * B) (B' * A') :=
  fun x y => (hA x (B y)).trans (hB (A' x) y)
theorem isSelfAdjointOp_fivePointCombo {T U V : H →L[ℂ] H} (hT : IsSelfAdjointOp T)
    (hU : IsAdjointPair U V) (hV : IsAdjointPair V U) (cU : T * U = U * T) (cV : T * V = V * T) :
    IsSelfAdjointOp ((1 - T) ^ 2 - T * ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V)) := by
  have h₁ : IsAdjointPair (1 - T) (1 - T) := isAdjointPair_sub isAdjointPair_one hT
  have h₂ : IsAdjointPair ((1 - T) ^ 2) ((1 - T) ^ 2) := by
    rw [pow_two]
    exact isAdjointPair_mul h₁ h₁
  have h₃ : IsAdjointPair ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V) ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V) := by
    rw [two_smul]
    have h := isAdjointPair_sub (isAdjointPair_sub (isAdjointPair_add (isAdjointPair_one (H := H)) isAdjointPair_one) hU) hV
    rwa [sub_right_comm (1 + 1 : H →L[ℂ] H) V U] at h
  have h₄ : T * ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V) = ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V) * T := by
    simp only [mul_sub, sub_mul, cU, cV, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have h₅ : IsAdjointPair (T * ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V))
      (T * ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V)) := by
    have h := isAdjointPair_mul hT h₃
    rwa [← h₄] at h
  exact isAdjointPair_sub h₂ h₅
theorem fivePointCombo_expand (T U V : H →L[ℂ] H) :
    (1 - T) ^ 2 - T * ((2 : ℂ) • (1 : H →L[ℂ] H) - U - V) =
      1 - T - T - T - T + T * T + T * U + T * V := by
  rw [two_smul]
  noncomm_ring
end Adjoints
section Multiplier
def fivePointMultiplier (t : ℝ≥0) (p : EnergyMomentumLine) : ℝ :=
  1 - 4 * Real.exp (-(t : ℝ) * (p.1 : ℝ)) + Real.exp (-(t : ℝ) * (p.1 : ℝ)) ^ 2 +
    2 * Real.exp (-(t : ℝ) * (p.1 : ℝ)) * Real.cos ((t : ℝ) * p.2)
theorem continuous_fivePointMultiplier (t : ℝ≥0) : Continuous (fivePointMultiplier t) := by
  unfold fivePointMultiplier
  fun_prop
theorem abs_fivePointMultiplier_le_eight (t : ℝ≥0) (p : EnergyMomentumLine) : |fivePointMultiplier t p| ≤ 8 := by
  have hx₀ : 0 < Real.exp (-(t : ℝ) * (p.1 : ℝ)) := Real.exp_pos _
  have hx₁ : Real.exp (-(t : ℝ) * (p.1 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg t.2 p.1.2
    simp only [NNReal.val_eq_coe] at this
    linarith
  have hc₀ := Real.neg_one_le_cos ((t : ℝ) * p.2)
  have hc₁ := Real.cos_le_one ((t : ℝ) * p.2)
  unfold fivePointMultiplier
  set x := Real.exp (-(t : ℝ) * (p.1 : ℝ))
  set c := Real.cos ((t : ℝ) * p.2)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hx₀.le (sub_nonneg.2 hc₁), mul_nonneg hx₀.le (by linarith : 0 ≤ c + 1), mul_nonneg hx₀.le (sub_nonneg.2 hx₁)]
theorem fivePointMultiplier_eq_sinh_sin (t : ℝ≥0) (p : EnergyMomentumLine) :
    fivePointMultiplier t p = 4 * Real.exp (-(t : ℝ) * (p.1 : ℝ)) *
      (Real.sinh ((t : ℝ) * (p.1 : ℝ) / 2) ^ 2 - Real.sin ((t : ℝ) * p.2 / 2) ^ 2) := by
  set y := (t : ℝ) * (p.1 : ℝ) / 2 with hy
  set θ := (t : ℝ) * p.2 / 2 with hθ
  have hc : Real.cos ((t : ℝ) * p.2) = 1 - 2 * Real.sin θ ^ 2 := by
    rw [show (t : ℝ) * p.2 = 2 * θ by rw [hθ]; ring, Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq θ]
  have hb : Real.exp (-(t : ℝ) * (p.1 : ℝ)) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    rw [hy]
    ring
  have hab : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp
  have hS : 4 * (Real.exp (-y) * Real.exp (-y)) * Real.sinh y ^ 2 =
      (1 - Real.exp (-y) * Real.exp (-y)) ^ 2 := by
    rw [Real.sinh_eq, ← hab]
    ring
  unfold fivePointMultiplier
  rw [hc, hb]
  linear_combination -hS
theorem fivePointMultiplier_neg_iff (t : ℝ≥0) (p : EnergyMomentumLine) :
    fivePointMultiplier t p < 0 ↔ p ∉ sinhSinRegion t := by
  have hs : 0 ≤ Real.sinh ((t : ℝ) * (p.1 : ℝ) / 2) := by
    rw [Real.sinh_nonneg_iff]
    have := mul_nonneg t.2 p.1.2
    simp only [NNReal.val_eq_coe] at this
    linarith
  rw [fivePointMultiplier_eq_sinh_sin]
  change _ ↔ ¬ (|Real.sin ((t : ℝ) * p.2 / 2)| ≤ Real.sinh ((t : ℝ) * (p.1 : ℝ) / 2))
  rw [not_le, ← sq_lt_sq₀ hs (abs_nonneg _), sq_abs]
  have hx : 0 < 4 * Real.exp (-(t : ℝ) * (p.1 : ℝ)) := by positivity
  rw [mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨hx, by linarith⟩
theorem exp_I_mul_add_exp_I_mul_neg (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) + Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) =
      ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [mul_comm Complex.I, mul_comm Complex.I, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring
theorem ofReal_fivePointMultiplier (t : ℝ≥0) (p : EnergyMomentumLine) :
    ((fivePointMultiplier t p : ℝ) : ℂ) =
      laplaceFourierExpLine 0 0 p + (-4 : ℂ) * laplaceFourierExpLine t 0 p + laplaceFourierExpLine (2 * t) 0 p +
        laplaceFourierExpLine t (t : ℝ) p + laplaceFourierExpLine t (-(t : ℝ)) p := by
  have h₀ : laplaceFourierExpLine 0 0 p = 1 := by simp [laplaceFourierExpLine]
  have h₁ : laplaceFourierExpLine t 0 p = ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) := by
    simp [laplaceFourierExpLine]
  have h₂ : laplaceFourierExpLine (2 * t) 0 p = ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) ^ 2 : ℝ) : ℂ) := by
    have e : Real.exp (-(t : ℝ) * (p.1 : ℝ)) ^ 2 = Real.exp (-((2 * t : ℝ≥0) : ℝ) * (p.1 : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    simp [laplaceFourierExpLine]
  have h₃ : ∀ s : ℝ, laplaceFourierExpLine t s p = ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((s * p.2 : ℝ) : ℂ)) := by
    intro s
    rw [laplaceFourierExpLine, Complex.exp_add, Complex.ofReal_exp]
  have h₄ := exp_I_mul_add_exp_I_mul_neg ((t : ℝ) * p.2)
  rw [h₀, h₁, h₂, h₃ (t : ℝ), h₃ (-(t : ℝ)), add_assoc _ (_ * _) (_ * _), ← mul_add, neg_mul (t : ℝ) p.2, h₄]
  simp only [fivePointMultiplier]
  push_cast
  ring
theorem isBoundedMeasurable_laplaceFourierExpLine (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (laplaceFourierExpLine t s) := by apply _root_.YangMills.Construction.EnergyMomentum.JointSpectral.Existence.isBoundedMeasurable_laplaceFourierExpLine <;> assumption
end Multiplier
section BoundedMeasurable
variable {Y : Type*} [MeasurableSpace Y]
theorem isBoundedMeasurable_add_fn {f g : Y → ℂ} (hf : IsBoundedMeasurable f)
    (hg : IsBoundedMeasurable g) : IsBoundedMeasurable (f + g) := by
  obtain ⟨mf, c, hc⟩ := hf
  obtain ⟨mg, d, hd⟩ := hg
  exact ⟨mf.add mg, c + d, fun y => (norm_add_le _ _).trans (add_le_add (hc y) (hd y))⟩
theorem isBoundedMeasurable_const_smul (α : ℂ) {f : Y → ℂ} (hf : IsBoundedMeasurable f) :
    IsBoundedMeasurable (α • f) := by
  obtain ⟨mf, c, hc⟩ := hf
  refine ⟨mf.const_smul α, ‖α‖ * c, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hc y) (norm_nonneg _)
end BoundedMeasurable
section Reconstruction
variable (σ : Tuple → ℝ) (h : ReflectionPositiveAt timeZeroMirror σ)
theorem spatialTranslationRep_zero_eq_one (hU : SpatialRepProps σ h) :
    spatialTranslationRep σ h 0 = 1 := by
  refine ContinuousLinearMap.ext fun ψ => (hU.isUnitary 0).bijective.1 ?_
  have e := hU.add 0 0
  rw [add_zero] at e
  exact congrArg (fun B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h => B ψ) e
theorem isAdjointPair_spatialTranslationRep_neg (hF : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (hU : SpatialRepProps σ h) (y : Momentum3) :
    IsAdjointPair (spatialTranslationRep σ h y) (spatialTranslationRep σ h (-y)) := by
  obtain ⟨U', h₁, _, h₃⟩ := (hF.2.2.1 (ReconstructionSpace σ h)).2.2.2 _ (hU.isUnitary y)
  have e : spatialTranslationRep σ h y * spatialTranslationRep σ h (-y) = 1 := by
    rw [hU.add, add_neg_cancel, spatialTranslationRep_zero_eq_one σ h hU]
  have e' : U' = spatialTranslationRep σ h (-y) := by
    calc U' = U' * (spatialTranslationRep σ h y * spatialTranslationRep σ h (-y)) := by
          rw [e, mul_one]
      _ = spatialTranslationRep σ h (-y) := by rw [← mul_assoc, h₁, one_mul]
  exact e' ▸ h₃
theorem shiftedPairing_congr_vec (Z : combsSupportedIn upperHalfSpace) {v v' : Space} (e : v = v')
    (hv : 0 ≤ v timeAxis) (hv' : 0 ≤ v' timeAxis) :
    shiftedPairing σ Z v hv = shiftedPairing σ Z v' hv' := by
  subst e
  rfl
theorem shiftedPairing_timeShiftVec_eq_inner (hT : TransferSemigroupProps σ h) (Z : combsSupportedIn upperHalfSpace)
    (t : ℝ≥0) (hv : 0 ≤ timeShiftVec t timeAxis) :
    shiftedPairing σ Z (timeShiftVec t) hv =
      ⟪toReconstruction σ h Z, transferSemigroup σ h t (toReconstruction σ h Z)⟫_ℂ := by
  rw [hT.isTransferSemigroup t Z, inner_toReconstruction]
  rfl
theorem shiftedPairing_zero_eq_inner (hT : TransferSemigroupProps σ h) (Z : combsSupportedIn upperHalfSpace)
    (hv : 0 ≤ (0 : Space) timeAxis) :
    shiftedPairing σ Z 0 hv = ⟪toReconstruction σ h Z, toReconstruction σ h Z⟫_ℂ := by
  have e : timeShiftVec 0 = 0 := by simp [timeShiftVec]
  have h₀ : 0 ≤ timeShiftVec 0 timeAxis := by rw [e]; exact hv
  rw [shiftedPairing_congr_vec σ Z e.symm hv h₀, shiftedPairing_timeShiftVec_eq_inner σ h hT Z 0 h₀, hT.zero]
  rfl
theorem fivePointExpr_eq_inner_fivePointOp (hT : TransferSemigroupProps σ h) (hM : MatrixElementProps σ h) (i : Fin 3)
    (Z : combsSupportedIn upperHalfSpace) (t : ℝ≥0) :
    fivePointExpr σ i Z t = ⟪toReconstruction σ h Z,
      fivePointOp σ h i t (toReconstruction σ h Z)⟫_ℂ := by
  have e₃ : ∀ y : Momentum3,
      shiftedPairing σ Z (timeShiftVec t + embedSpatial y)
        (timeShiftVec_add_embedSpatial_timeAxis_nonneg t y) =
      ⟪toReconstruction σ h Z, transferSemigroup σ h t
        (spatialTranslationRep σ h y (toReconstruction σ h Z))⟫_ℂ :=
    fun y => (hM.inner_eq Z Z t y).symm
  have h₂ : transferSemigroup σ h t * transferSemigroup σ h t =
      transferSemigroup σ h (2 * t) := by
    rw [hT.add, two_mul]
  unfold fivePointExpr fivePointOp
  rw [fivePointCombo_expand, h₂, shiftedPairing_zero_eq_inner σ h hT, shiftedPairing_timeShiftVec_eq_inner σ h hT,
    shiftedPairing_timeShiftVec_eq_inner σ h hT, e₃, e₃]
  have hm : ∀ (A B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h)
      (ψ : ReconstructionSpace σ h), (A * B) ψ = A (B ψ) := fun _ _ _ => rfl
  simp only [add_apply, sub_apply, ContinuousLinearMap.one_apply, inner_add_right, inner_sub_right,
    hm]
  ring
theorem opGe_zero_of_nonneg_on_dense_classes (hF : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (B : ReconstructionSpace σ h →L[ℂ] ReconstructionSpace σ h)
    (hB : IsSelfAdjointOp B)
    (hpos : ∀ Z, 0 ≤ (⟪toReconstruction σ h Z, B (toReconstruction σ h Z)⟫_ℂ).re) :
    OpGe B (scalarOp 0) := by
  have hd : Dense (Set.range (toReconstruction σ h)) :=
    (hF.2.1 (combsSupportedIn upperHalfSpace) (reflForm σ)
      (isPosSemidef_reflForm h)).2.2.1
  have hD : Dense ((LinearMap.range (toReconstruction σ h) :
      Submodule ℂ (ReconstructionSpace σ h)) : Set (ReconstructionSpace σ h)) := by
    rw [LinearMap.coe_range]
    exact hd
  refine (hF.2.2.2.1 (ReconstructionSpace σ h) _ hD).2.2.2 B hB ?_
  rintro ⟨_, Z, rfl⟩
  exact hpos Z
theorem fivePointOp_eq_boundedCalculus (hC : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hT : TransferSemigroupProps σ h) (hU : SpatialRepProps σ h) (i : Fin 3)
    (F : SpectralMeasure EnergyMomentumLine (ReconstructionSpace σ h))
    (hm : IsAxisSpectralMeasure σ h i F) (t : ℝ≥0) :
    fivePointOp σ h i t = F.boundedCalculus fun p => ((fivePointMultiplier t p : ℝ) : ℂ) := by
  have hB := (hC EnergyMomentumLine (ReconstructionSpace σ h) F).2.1
  have b := isBoundedMeasurable_laplaceFourierExpLine
  have e : (fun p => ((fivePointMultiplier t p : ℝ) : ℂ)) =
      laplaceFourierExpLine 0 0 + (-4 : ℂ) • laplaceFourierExpLine t 0 + laplaceFourierExpLine (2 * t) 0 +
        laplaceFourierExpLine t (t : ℝ) + laplaceFourierExpLine t (-(t : ℝ)) :=
    funext fun p => by simpa using ofReal_fivePointMultiplier t p
  have b₀ := isBoundedMeasurable_const_smul (-4 : ℂ) (b t 0)
  have b₁ := isBoundedMeasurable_add_fn (b 0 0) b₀
  have b₂ := isBoundedMeasurable_add_fn b₁ (b (2 * t) 0)
  have b₃ := isBoundedMeasurable_add_fn b₂ (b t (t : ℝ))
  rw [e, hB.add _ _ b₃ (b _ _), hB.add _ _ b₂ (b _ _), hB.add _ _ b₁ (b _ _),
    hB.add _ _ (b _ _) b₀, hB.smul _ _ (b _ _), ← hm 0 0, ← hm t 0,
    ← hm (2 * t) 0, ← hm t (t : ℝ), ← hm t (-(t : ℝ))]
  simp only [zero_smul, spatialTranslationRep_zero_eq_one σ h hU, hT.zero, mul_one]
  unfold fivePointOp
  rw [fivePointCombo_expand, hT.add, ← two_mul]
  module
theorem isCarriedBy_sinhSinRegion_of_opGe (hC : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hT : TransferSemigroupProps σ h) (hU : SpatialRepProps σ h) (i : Fin 3)
    (F : SpectralMeasure EnergyMomentumLine (ReconstructionSpace σ h))
    (hm : IsAxisSpectralMeasure σ h i F) (t : ℝ≥0)
    (hJ : OpGe (fivePointOp σ h i t) (scalarOp 0)) :
    F.IsCarriedBy ⟨sinhSinRegion t, measurableSet_sinhSinRegion t⟩ := by
  rw [fivePointOp_eq_boundedCalculus σ h hC hT hU i F hm t] at hJ
  have hv := (hC EnergyMomentumLine (ReconstructionSpace σ h) F).2.2.2.1.apply_neg_eq_zero
    (fivePointMultiplier t) (continuous_fivePointMultiplier t).measurable
    ⟨8, abs_fivePointMultiplier_le_eight t⟩ hJ
  have e : (⟨(sinhSinRegion t)ᶜ, (measurableSet_sinhSinRegion t).compl⟩ :
      BorelSubsets EnergyMomentumLine) = ⟨{y | fivePointMultiplier t y < 0},
        measurableSet_lt (continuous_fivePointMultiplier t).measurable measurable_const⟩ :=
    Subtype.ext (Set.ext fun p => (fivePointMultiplier_neg_iff t p).symm)
  change F ⟨(sinhSinRegion t)ᶜ, (measurableSet_sinhSinRegion t).compl⟩ = 0
  rw [e]
  exact hv
end Reconstruction
section SmallTimes
theorem exists_seq_tendsto_zero_of_accPt {D : Set ℝ≥0} (hD : AccPt (0 : ℝ≥0) (𝓟 D)) :
    ∃ s : ℕ → ℝ≥0, Tendsto s atTop (𝓝 0) ∧ ∀ n, s n ≠ 0 ∧ s n ∈ D := by
  rw [accPt_iff_frequently] at hD
  exact exists_seq_forall_of_frequently hD
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isCarriedBy_energyGeAbsMomentum_of_seq
    (hK : YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality.SinhDominatesAbsSinIffStatement)
    (F : SpectralMeasure EnergyMomentumLine H)
    (hV : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.ValuesAndDiagMeasures F)
    (s : ℕ → ℝ≥0) (hs : Tendsto s atTop (𝓝 0)) (hne : ∀ n, s n ≠ 0)
    (hc : ∀ n, F.IsCarriedBy ⟨sinhSinRegion (s n), measurableSet_sinhSinRegion (s n)⟩) :
    F.IsCarriedBy ⟨energyGeAbsMomentum, measurableSet_energyGeAbsMomentum⟩ := by
  have hU := hV.apply_iUnion
    (fun n => ⟨(sinhSinRegion (s n))ᶜ, (measurableSet_sinhSinRegion (s n)).compl⟩) hc
  have ht : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 hs
  have hsub : energyGeAbsMomentumᶜ ⊆ ⋃ n, (sinhSinRegion (s n))ᶜ := by
    intro p hp
    by_contra hq
    simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at hq
    refine hp ((hK 13 ⟨⟨6, by norm_num⟩, le_rfl⟩ (p.1 : ℝ) p.2 p.1.2).2.1
      (range fun n => (s n : ℝ)) ?_ ?_ ?_)
    · rintro _ ⟨n, rfl⟩
      exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hne n))
    · rw [accPt_iff_frequently]
      exact ht.frequently (Frequently.of_forall fun n =>
        ⟨NNReal.coe_ne_zero.2 (hne n), ⟨n, rfl⟩⟩)
    · rintro _ ⟨n, rfl⟩
      exact hq n
  have hm := F.map_inter ⟨energyGeAbsMomentumᶜ, measurableSet_energyGeAbsMomentum.compl⟩
    ⟨⋃ n, (sinhSinRegion (s n))ᶜ,
      MeasurableSet.iUnion fun n => (measurableSet_sinhSinRegion (s n)).compl⟩
  have e : (⟨energyGeAbsMomentumᶜ ∩ ⋃ n, (sinhSinRegion (s n))ᶜ,
      measurableSet_energyGeAbsMomentum.compl.inter
        (MeasurableSet.iUnion fun n => (measurableSet_sinhSinRegion (s n)).compl)⟩ :
      BorelSubsets EnergyMomentumLine) =
      ⟨energyGeAbsMomentumᶜ, measurableSet_energyGeAbsMomentum.compl⟩ :=
    Subtype.ext (inter_eq_left.2 hsub)
  rw [e, hU, mul_zero] at hm
  exact hm.symm
end SmallTimes
section Measures
theorem ennreal_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact h.trans le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (pow_two a).symm
      _ ≤ 1 + a ^ 2 := le_add_self
theorem enorm_complex_ofReal_eq (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
variable {Y : Type*} [MeasurableSpace Y]
theorem integrable_of_lintegral_enorm_sq_lt_top (m : Measure Y) [IsFiniteMeasure m] {f : Y → ℝ}
    (hf : Measurable f) (h : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂m < ∞) : Integrable f m := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have h₁ : ∫⁻ y, ‖f y‖ₑ ∂m ≤ ∫⁻ y, (1 + ‖f y‖ₑ ^ 2) ∂m :=
    lintegral_mono fun y => ennreal_le_one_add_sq _
  rw [lintegral_add_left measurable_const, lintegral_const] at h₁
  exact h₁.trans_lt (ENNReal.add_lt_top.2 ⟨by simp [measure_lt_top], h⟩)
end Measures
section Operators
open YangMills.Construction.EuclideanSpectral.SpectralMeasure YangMills.Construction.EuclideanSpectral.FunctionalCalculus
variable {Y H : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem diagMeasure_eq_zero_of_apply_eq_zero (G : SpectralMeasure Y H) (Δ : BorelSubsets Y) (h : G Δ = 0)
    (ψ : H) : G.diagMeasure ψ Δ.1 = 0 := by
  rw [diagMeasure, Measure.ofMeasurable_apply _ Δ.2]
  change ENNReal.ofReal (G.diagMass ψ Δ).re = 0
  simp [diagMass, h]
theorem mem_calculusDomain_of_mem_domain (G : SpectralMeasure Y H) (hB : UnboundedCalculusLaws G)
    {φ : Y → ℂ} (hφ : Measurable φ) {ψ : H} (h : ψ ∈ (G.calculusOperator φ).domain) :
    ψ ∈ G.calculusDomain φ := by
  rw [← (hB.isCalculusOperator φ hφ).1]
  exact h
theorem mem_domain_of_mem_calculusDomain (G : SpectralMeasure Y H) (hB : UnboundedCalculusLaws G)
    {φ : Y → ℂ} (hφ : Measurable φ) {ψ : H} (h : ψ ∈ G.calculusDomain φ) :
    ψ ∈ (G.calculusOperator φ).domain := by
  rw [← (hB.isCalculusOperator φ hφ).1] at h
  exact h
theorem mem_calculusDomain_of_ae_norm_le (G : SpectralMeasure Y H) {φ φ' : Y → ℂ} {ψ : H}
    (hle : ∀ᵐ y ∂G.diagMeasure ψ, ‖φ y‖ ≤ ‖φ' y‖) (hψ : ψ ∈ G.calculusDomain φ') :
    ψ ∈ G.calculusDomain φ := by
  refine lt_of_le_of_lt (lintegral_mono_ae (hle.mono fun y hy => ?_)) hψ
  have : ‖φ y‖ₑ ≤ ‖φ' y‖ₑ := enorm_le_iff_norm_le.2 hy
  gcongr
theorem inner_calculusOperator_eq_integral (G : SpectralMeasure Y H) (hB : UnboundedCalculusLaws G)
    {φ : Y → ℂ} (hφ : Measurable φ) (ψ : H) (h : ψ ∈ (G.calculusOperator φ).domain) :
    ⟪ψ, G.calculusOperator φ ⟨ψ, h⟩⟫_ℂ = ∫ y, φ y ∂G.diagMeasure ψ := by
  rw [(hB.isCalculusOperator φ hφ).2 ⟨ψ, h⟩]
  exact hB.inner_eq φ hφ ψ (mem_calculusDomain_of_mem_domain G hB hφ h)
end Operators
section Cone
open YangMills.Construction.EuclideanSpectral.SpectralMeasure YangMills.Construction.EuclideanSpectral.FunctionalCalculus
theorem energyCoord_measurable : Measurable coordEnergy := by apply _root_.YangMills.Construction.EnergyMomentum.GeneratorsProof.measurable_energyCoord <;> assumption
theorem continuous_momentumComponent (i : Fin 3) : Continuous fun p : EnergyMomentumSpace => p.2 i :=
  (EuclideanSpace.proj i).continuous.comp continuous_snd
theorem momentumCoord_measurable (i : Fin 3) : Measurable (coordMomentum i) :=
  (Complex.continuous_ofReal.comp (continuous_momentumComponent i)).measurable
theorem absMomentumCoord_measurable (i : Fin 3) : Measurable (absMomentumCoord i) :=
  (Complex.continuous_ofReal.comp (continuous_momentumComponent i).abs).measurable
theorem expCoordMomentum_isBoundedMeasurable (i : Fin 3) (u : ℝ) :
    IsBoundedMeasurable (expCoordMomentum i u) := by
  refine ⟨?_, 1, fun p => ?_⟩
  · have : Continuous (expCoordMomentum i u) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_momentumComponent i))))
    exact this.measurable
  · simp [expCoordMomentum, Complex.norm_exp]
theorem energyGeAbsMomentum_isClosed : IsClosed energyGeAbsMomentum :=
  isClosed_le (by fun_prop) (by fun_prop)
variable (σ : Tuple → ℝ) (hσ : ReconstructionData σ) (i : Fin 3)
theorem ae_abs_momentum_le_energy (hC : FunctionalCalculusHolds)
    (hco : AxisMeasureProps σ hσ.reflectionPositive i)
    (hdom : EnergyDominatesMomentum σ hσ i)
    (ψ : ReconstructionSpace σ hσ.reflectionPositive) :
    ∀ᵐ p ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ,
      |p.2 i| ≤ (p.1 : ℝ) := by
  have hcar := ((hC EnergyMomentumLine _ (axisSpectralMeasure σ hσ.reflectionPositive i)
    ).2.2.2.2.2.2.supp_subset_iff energyGeAbsMomentum energyGeAbsMomentum_isClosed).1 hdom
  rw [hco.eq_pushforward] at hcar
  have h₀ := diagMeasure_eq_zero_of_apply_eq_zero (jointSpectralMeasure σ hσ.reflectionPositive)
    ⟨projMomentum i ⁻¹' energyGeAbsMomentumᶜ,
      measurable_projMomentum i energyGeAbsMomentum_isClosed.measurableSet.compl⟩
    hcar ψ
  filter_upwards [compl_mem_ae_iff.2 h₀] with p hp
  exact not_not.1 hp
theorem domainComparison_of_energyDominatesMomentum (hC : FunctionalCalculusHolds)
    (hco : AxisMeasureProps σ hσ.reflectionPositive i)
    (hdom : EnergyDominatesMomentum σ hσ i) : DomainComparison σ hσ i := by
  have hAll := hC EnergyMomentumSpace (ReconstructionSpace σ hσ.reflectionPositive)
    (jointSpectralMeasure σ hσ.reflectionPositive)
  have hB := hAll.2.2.2.2.2.1
  have hV := hAll.1
  have hae := ae_abs_momentum_le_energy σ hσ i hC hco hdom
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ
    refine mem_domain_of_mem_calculusDomain _ hB (momentumCoord_measurable i) (mem_calculusDomain_of_ae_norm_le _
      ((hae ψ).mono fun p hp => ?_) (mem_calculusDomain_of_mem_domain _ hB energyCoord_measurable hψ))
    simpa [coordMomentum, coordEnergy] using hp
  · refine le_antisymm ?_ ?_
    · intro ψ hψ
      refine mem_domain_of_mem_calculusDomain _ hB (absMomentumCoord_measurable i) (mem_calculusDomain_of_ae_norm_le _
        (Eventually.of_forall fun p => ?_)
        (mem_calculusDomain_of_mem_domain _ hB (momentumCoord_measurable i) hψ))
      simp [coordMomentum, absMomentumCoord]
    · intro ψ hψ
      refine mem_domain_of_mem_calculusDomain _ hB (momentumCoord_measurable i) (mem_calculusDomain_of_ae_norm_le _
        (Eventually.of_forall fun p => ?_)
        (mem_calculusDomain_of_mem_domain _ hB (absMomentumCoord_measurable i) hψ))
      simp [coordMomentum, absMomentumCoord]
  · intro ψ hH hP
    haveI := hV.isFiniteMeasure ψ
    have iE : ⟪ψ, hamiltonianOp σ hσ ⟨ψ, hH⟩⟫_ℂ =
        ∫ p, coordEnergy p ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ :=
      inner_calculusOperator_eq_integral _ hB energyCoord_measurable ψ hH
    have iP : ⟪ψ, absMomentumOp σ hσ i ⟨ψ, hP⟩⟫_ℂ =
        ∫ p, absMomentumCoord i p
          ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ :=
      inner_calculusOperator_eq_integral _ hB (absMomentumCoord_measurable i) ψ hP
    have dE := mem_calculusDomain_of_mem_domain _ hB energyCoord_measurable hH
    change ∫⁻ y, ‖coordEnergy y‖ₑ ^ 2
      ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ < ∞ at dE
    simp only [coordEnergy, enorm_complex_ofReal_eq] at dE
    have hint := integrable_of_lintegral_enorm_sq_lt_top _ (f := fun p : EnergyMomentumSpace => (p.1 : ℝ))
      (NNReal.continuous_coe.comp continuous_fst).measurable dE
    rw [iE, iP]
    simp only [coordEnergy, absMomentumCoord]
    rw [integral_complex_ofReal, integral_complex_ofReal, Complex.real_le_real]
    exact integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _) hint (hae ψ)
theorem kernelTranslationInvariant_of_energyDominatesMomentum
    (hC : FunctionalCalculusHolds)
    (hco : AxisMeasureProps σ hσ.reflectionPositive i)
    (hdom : EnergyDominatesMomentum σ hσ i) : KernelTranslationInvariant σ hσ i := by
  rintro ψ ⟨hd, h0⟩ u
  have hAll := hC EnergyMomentumSpace (ReconstructionSpace σ hσ.reflectionPositive)
    (jointSpectralMeasure σ hσ.reflectionPositive)
  have hB := hAll.2.2.2.2.2.1
  have hV := hAll.1
  have hBF := hAll.2.1
  haveI := hV.isFiniteMeasure ψ
  have dE := mem_calculusDomain_of_mem_domain _ hB energyCoord_measurable hd
  have hl : (jointSpectralMeasure σ hσ.reflectionPositive).calculusLimit coordEnergy ψ = 0 :=
    ((hB.isCalculusOperator coordEnergy energyCoord_measurable).2 ⟨ψ, hd⟩).symm.trans h0
  have hn := hB.norm_sq coordEnergy energyCoord_measurable ψ dE
  rw [hl, norm_zero] at hn
  have hi : Integrable (fun y => ‖coordEnergy y‖ ^ 2)
      ((jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ) := by
    refine ⟨(energyCoord_measurable.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    have e : ∫⁻ y, ‖‖coordEnergy y‖ ^ 2‖ₑ
        ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ =
        ∫⁻ y, ‖coordEnergy y‖ₑ ^ 2
          ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ :=
      lintegral_congr fun y => by rw [enorm_pow, enorm_norm]
    change ∫⁻ y, ‖‖coordEnergy y‖ ^ 2‖ₑ
        ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ < ∞
    rw [e]
    exact dE
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hi).1
    (by simpa using hn.symm)
  have hone : ∀ᵐ p ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ,
      expCoordMomentum i u p = 1 := by
    filter_upwards [hz, ae_abs_momentum_le_energy σ hσ i hC hco hdom ψ] with p h₁ h₂
    have hE : (p.1 : ℝ) = 0 := by simpa [coordEnergy] using h₁
    have hq : p.2 i = 0 := abs_nonpos_iff.1 (h₂.trans hE.le)
    simp [expCoordMomentum, hq]
  have b₁ : IsBoundedMeasurable (1 : EnergyMomentumSpace → ℂ) := ⟨measurable_const, 1, fun _ => by simp⟩
  have bc := expCoordMomentum_isBoundedMeasurable i u
  have bs := isBoundedMeasurable_const_smul (-1 : ℂ) b₁
  have hone' : (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus 1 = 1 := by
    have e := hBF.indicator ⟨univ, MeasurableSet.univ⟩
    rw [(jointSpectralMeasure σ hσ.reflectionPositive).map_univ] at e
    simpa [Set.indicator_univ] using e
  have hf : (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus
      (expCoordMomentum i u + (-1 : ℂ) • (1 : EnergyMomentumSpace → ℂ)) =
      (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus
        (expCoordMomentum i u) + (-1 : ℂ) • 1 := by
    rw [hBF.add _ _ bc bs, hBF.smul _ _ b₁, hone']
  have hn₂ := hBF.norm_sq _ (isBoundedMeasurable_add_fn bc bs) ψ
  have hz₂ : ∫ y, ‖(expCoordMomentum i u + (-1 : ℂ) • (1 : EnergyMomentumSpace → ℂ)) y‖ ^ 2
      ∂(jointSpectralMeasure σ hσ.reflectionPositive).diagMeasure ψ = 0 :=
    integral_eq_zero_of_ae (hone.mono fun p hp => by simp [hp])
  rw [hz₂, hf] at hn₂
  have h₃ := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hn₂)
  have h₄ : (jointSpectralMeasure σ hσ.reflectionPositive).boundedCalculus
      (expCoordMomentum i u) ψ + -ψ = 0 := by
    simpa using h₃
  exact add_neg_eq_zero.1 h₄
end Cone
theorem fivePointConeTheorem_holds (hC : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hF : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (hK : YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality.SinhDominatesAbsSinIffStatement)
    (hR : DenseTimeReconstructionHolds) : FivePointConeTheorem := by
  intro σ hσ i
  obtain ⟨_, _, hrest⟩ := hR.2 σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, hM, hCo, _⟩ := hrest hσ.contractsOnDenseTimes
  have hco := hCo i
  have hm := hco.isAxisSpectralMeasure
  have hcons : EnergyDominatesMomentum σ hσ i →
      DomainComparison σ hσ i ∧ KernelTranslationInvariant σ hσ i := fun hd =>
    ⟨domainComparison_of_energyDominatesMomentum σ hσ i hC hco hd,
      kernelTranslationInvariant_of_energyDominatesMomentum σ hσ i hC hco hd⟩
  refine ⟨fun D _ hacc hfive => ?_, hcons⟩
  have hadj : ∀ t : ℝ≥0, IsAdjointPair
      (spatialTranslationRep σ hσ.reflectionPositive
        ((t : ℝ) • EuclideanSpace.single i (1 : ℝ)))
      (spatialTranslationRep σ hσ.reflectionPositive
        ((-(t : ℝ)) • EuclideanSpace.single i (1 : ℝ))) := fun t => by
    rw [neg_smul]
    exact isAdjointPair_spatialTranslationRep_neg σ _ hF hU _
  have hadj' : ∀ t : ℝ≥0, IsAdjointPair
      (spatialTranslationRep σ hσ.reflectionPositive
        ((-(t : ℝ)) • EuclideanSpace.single i (1 : ℝ)))
      (spatialTranslationRep σ hσ.reflectionPositive
        ((t : ℝ) • EuclideanSpace.single i (1 : ℝ))) := fun t => by
    have h := isAdjointPair_spatialTranslationRep_neg σ _ hF hU ((-(t : ℝ)) • EuclideanSpace.single i (1 : ℝ))
    rwa [neg_smul, neg_neg, ← neg_smul] at h
  have hsa : ∀ t : ℝ≥0,
      IsSelfAdjointOp (fivePointOp σ hσ.reflectionPositive i t) := fun t =>
    isSelfAdjointOp_fivePointCombo (hT.isSelfAdjoint t) (hadj t) (hadj' t) (hU.commutes t _)
      (hU.commutes t _)
  have hJ : ∀ t ∈ D,
      OpGe (fivePointOp σ hσ.reflectionPositive i t) (scalarOp 0) :=
    fun t ht => opGe_zero_of_nonneg_on_dense_classes σ _ hF _ (hsa t) fun Z => by
      rw [← fivePointExpr_eq_inner_fivePointOp σ _ hT hM i Z t]
      exact (Complex.le_def.1 (hfive Z t ht)).1
  have hb : CarriedBySinhRegions σ hσ i D := fun t ht =>
    isCarriedBy_sinhSinRegion_of_opGe σ _ hC hT hU i _ hm t (hJ t ht)
  obtain ⟨s, hs, hsD⟩ := exists_seq_tendsto_zero_of_accPt hacc
  have hcone := isCarriedBy_energyGeAbsMomentum_of_seq hK _ (hC EnergyMomentumLine _ _).1 s hs (fun n => (hsD n).1)
    (fun n => hb _ (hsD n).2)
  have hdom : EnergyDominatesMomentum σ hσ i :=
    ((hC EnergyMomentumLine _ (axisSpectralMeasure σ hσ.reflectionPositive i)
      ).2.2.2.2.2.2.supp_subset_iff energyGeAbsMomentum
        energyGeAbsMomentum_isClosed).2 hcone
  exact ⟨⟨fun t _ Z => fivePointExpr_eq_inner_fivePointOp σ _ hT hM i Z t, fun t _ => hsa t,
    fun t _ => hadj' t, hJ⟩, hb, ⟨hcone, hdom⟩, (hcons hdom).1, (hcons hdom).2⟩
end YangMills.Construction.ReflectionPositivity.FivePointCone
