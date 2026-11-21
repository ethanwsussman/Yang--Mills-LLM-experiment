import YangMills.Construction.HilbertSpace.BoundedOperatorFacts
import YangMills.Construction.ReflectionPositiveLimits.ExponentialsOfTheGenerators
import YangMills.Construction.ReflectionPositiveLimits.FromFivePointInequalitiesToTheCone
import YangMills.Construction.ReflectionPositiveLimits.VacuumErgodicityAndClusteringInTime
import YangMills.Construction.ReflectionPositiveLimits.ZeroEnergyProjectionIsSpectral
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TimeClustering
open YangMills.Construction.ReflectionPositivity.FunctionalReconstruction
open YangMills.Construction.EuclideanSpectral
theorem tendsto_average_of_tendsto {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ}
    (hlim : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, f s) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 2) (by positivity)
  have hg : Continuous fun s => f s - L := hf.sub continuous_const
  obtain ⟨B, hB0, hBA⟩ : ∃ B : ℝ, 0 ≤ B ∧ A ≤ B := ⟨max A 0, le_max_right _ _, le_max_left _ _⟩
  set C : ℝ := |∫ s in (0 : ℝ)..B, (f s - L)| with hC
  refine ⟨max (B + 1) (2 * (C + 1) / ε), fun t ht => ?_⟩
  have ht₁ : B + 1 ≤ t := (le_max_left _ _).trans ht
  have ht₂ : 2 * (C + 1) / ε ≤ t := (le_max_right _ _).trans ht
  have htpos : 0 < t := by linarith
  have hBt : B ≤ t := by linarith
  have ht₃ : 2 * (C + 1) ≤ t * ε := (div_le_iff₀ hε).1 ht₂
  have hsplit : ∫ s in (0 : ℝ)..t, (f s - L) =
      (∫ s in (0 : ℝ)..B, (f s - L)) + ∫ s in B..t, (f s - L) :=
    (intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)).symm
  have hsub : ∫ s in (0 : ℝ)..t, (f s - L) = (∫ s in (0 : ℝ)..t, f s) - t * L := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    simp
  have hb : ‖∫ s in B..t, (f s - L)‖ ≤ ε / 2 * |t - B| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hBt] at hx
    have h₁ := hA x (hBA.trans hx.1.le)
    rw [Real.dist_eq] at h₁
    rw [Real.norm_eq_abs]
    exact h₁.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ t - B)] at hb
  have heq : (1 / t) * (∫ s in (0 : ℝ)..t, f s) - L =
      (1 / t) * ∫ s in (0 : ℝ)..t, (f s - L) := by
    rw [hsub, mul_sub, one_div, inv_mul_cancel_left₀ htpos.ne']
  rw [Real.dist_eq, heq, abs_mul, abs_of_pos (by positivity : 0 < 1 / t), one_div,
    inv_mul_lt_iff₀ htpos, hsplit]
  have h₂ : |(∫ s in (0 : ℝ)..B, (f s - L)) + ∫ s in B..t, (f s - L)| ≤
      C + ε / 2 * (t - B) := (abs_add_le _ _).trans (add_le_add le_rfl hb)
  linarith [mul_nonneg hB0 hε.le]
theorem comb_induction {p : combsSupportedIn upperHalfSpace → Prop}
    (hb : ∀ (X : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace), p (tupleToComb X hX))
    (h0 : p 0) (ha : ∀ Z W, p Z → p W → p (Z + W)) (hs : ∀ (c : ℂ) Z, p Z → p (c • Z))
    (Z : combsSupportedIn upperHalfSpace) : p Z := by
  obtain ⟨z, hz⟩ := Z
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    exact hb X hX
  | zero => exact h0
  | add x y hx hy ihx ihy => exact ha _ _ ihx ihy
  | smul a x hx ih => exact hs a _ ih
section InnerProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem ext_of_inner_tupleToComb (cl : combsSupportedIn upperHalfSpace →ₗ[ℂ] H)
    (hd : DenseRange cl) (A B : H →L[ℂ] H)
    (h : ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
      (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
      ⟪cl (tupleToComb X hX), A (cl (tupleToComb Y hY))⟫_ℂ =
        ⟪cl (tupleToComb X hX), B (cl (tupleToComb Y hY))⟫_ℂ) : A = B := by
  have h₁ : ∀ (Z : combsSupportedIn upperHalfSpace) (Y : Tuple)
      (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
      ⟪cl Z, A (cl (tupleToComb Y hY))⟫_ℂ = ⟪cl Z, B (cl (tupleToComb Y hY))⟫_ℂ := by
    intro Z Y hY
    induction Z using comb_induction with
    | hb X hX => exact h X Y hX hY
    | h0 => simp
    | ha Z W hZ hW => simp only [map_add, inner_add_left, hZ, hW]
    | hs c Z hZ => simp only [map_smul, inner_smul_left, hZ]
  have h₂ : ∀ Z W : combsSupportedIn upperHalfSpace, ⟪cl Z, A (cl W)⟫_ℂ = ⟪cl Z, B (cl W)⟫_ℂ := by
    intro Z W
    induction W using comb_induction with
    | hb Y hY => exact h₁ Z Y hY
    | h0 => simp
    | ha W W' hW hW' => simp only [map_add, inner_add_right, hW, hW']
    | hs c W hW => simp only [map_smul, inner_smul_right, hW]
  have h₃ : ∀ W, A (cl W) = B (cl W) := by
    intro W
    refine ext_inner_left ℂ fun χ => ?_
    refine hd.induction_on (p := fun χ => ⟪χ, A (cl W)⟫_ℂ = ⟪χ, B (cl W)⟫_ℂ) χ ?_ fun Z => h₂ Z W
    exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  ext ψ
  exact hd.induction_on (p := fun ψ => A ψ = B ψ) ψ (isClosed_eq A.continuous B.continuous) h₃
theorem apply_eq_inner_smul_of_fixedSet {P : H →L[ℂ] H} {Ω : H} (hP : IsOrthProjection P)
    (hΩ : ‖Ω‖ = 1) (hr : fixedSet P = range fun c : ℂ => c • Ω) (ψ : H) :
    P ψ = ⟪Ω, ψ⟫_ℂ • Ω := by
  have hi : P (P ψ) = P ψ := by
    rw [← mul_apply_eq_comp, hP.idempotent]
  have hm : P ψ ∈ range fun c : ℂ => c • Ω := by
    rw [← hr]
    exact hi
  obtain ⟨c, hc⟩ := hm
  have hc' : c • Ω = P ψ := hc
  have hΩr : Ω ∈ fixedSet P := by
    rw [hr]
    exact ⟨1, one_smul _ _⟩
  have hin : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have h₁ : ⟪Ω, P ψ⟫_ℂ = ⟪Ω, ψ⟫_ℂ := by
    rw [hP.selfAdjoint Ω ψ]
    rw [show P Ω = Ω from hΩr]
  have h₂ : c = ⟪Ω, ψ⟫_ℂ := by
    rw [← h₁, ← hc', inner_smul_right, hin, mul_one]
  rw [← hc', h₂]
theorem fixedSet_eq_ray_of_apply {P : H →L[ℂ] H} {Ω : H} (hΩ : ‖Ω‖ = 1)
    (h : ∀ ψ, P ψ = ⟪Ω, ψ⟫_ℂ • Ω) : fixedSet P = range fun c : ℂ => c • Ω := by
  have hin : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  ext ψ
  constructor
  · intro hψ
    refine ⟨⟪Ω, ψ⟫_ℂ, ?_⟩
    have h₁ : P ψ = ψ := hψ
    rw [h] at h₁
    exact h₁
  · rintro ⟨c, rfl⟩
    change P (c • Ω) = c • Ω
    rw [h, inner_smul_right, hin, mul_one]
end InnerProduct
theorem reflForm_tupleToComb_timeShift (σ : Tuple → ℝ) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace)
    (t : ℝ≥0) :
    reflForm σ (tupleToComb X hX) (timeShiftComb t (tupleToComb Y hY)) =
      (timeCorrelation σ hX hY t : ℂ) := by
  have hm₁ : pushComb timeZeroMirror.reflectIso (conjComb (basisOf X)) =
      basisOf (push timeZeroMirror.reflectIso X) := by
    simp [pushComb, basisOf, conjComb]
  have hm₂ : pushComb (EuclidIsometry.translate (timeShiftVec t)) (basisOf Y) =
      basisOf (push (EuclidIsometry.translate (timeShiftVec t)) Y) := by
    simp [pushComb, basisOf]
  change linearExt σ (concatBilin
    (pushComb timeZeroMirror.reflectIso (conjComb (basisOf X)))
    (pushComb (EuclidIsometry.translate (timeShiftVec t)) (basisOf Y))) = _
  rw [hm₁, hm₂]
  have hd := concatenable_timeShift hX hY t
  have hc : concatBilin (basisOf (push timeZeroMirror.reflectIso X))
      (basisOf (push (EuclidIsometry.translate (timeShiftVec t)) Y)) =
      basisOf (concat _ _ hd) := by
    simp [concatBilin, basisOf, concatBasis, hd]
  rw [hc]
  simp [linearExt, basisOf, timeCorrelation]
theorem inner_transferSemigroup_toReconstruction {σ : Tuple → ℝ}
    {h : ReflectionPositiveAt timeZeroMirror σ}
    (hT : DenseTimeReconstruction.TransferSemigroupProps σ h) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace)
    (t : ℝ≥0) :
    ⟪toReconstruction σ h (tupleToComb X hX),
      transferSemigroup σ h t (toReconstruction σ h (tupleToComb Y hY))⟫_ℂ =
      (timeCorrelation σ hX hY t : ℂ) := by
  rw [hT.isTransferSemigroup t _, inner_toReconstruction, reflForm_tupleToComb_timeShift]
theorem transferSemigroup_tendsto_and_kernel
    (hR : DenseTimeReconstruction.DenseTimeReconstructionHolds)
    (hS : YangMills.Construction.EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hG : YangMills.Construction.EnergyMomentum.Generators.GeneratorsTheorem)
    (hZ : GroundStateSpectral.GroundStateProjectionSpectral)
    (σ : Tuple → ℝ) (hσ : ReconstructionData σ) :
    TendstoStrongly atTop (transferSemigroup σ hσ.reflectionPositive)
        (groundStateProjection σ hσ) ∧
      ∀ ψ, ψ ∈ pmapKernel (hamiltonianOp σ hσ) ↔
        ∀ t, transferSemigroup σ hσ.reflectionPositive t ψ = ψ := by
  obtain ⟨-, hall⟩ := hR
  obtain ⟨-, -, hc⟩ := hall σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, -, -, hJ⟩ := hc hσ.contractsOnDenseTimes
  have hSC : YangMills.Construction.EnergyMomentum.IsContractionSemigroupWithUnitaryGroup
      (transferSemigroup σ hσ.reflectionPositive)
      (spatialTranslationRep σ hσ.reflectionPositive) :=
    { isSelfAdjoint := fun t => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
        fun x y => (hT.isSelfAdjoint t x y).symm
      norm_le_one := hT.isContraction
      semigroup_zero := hT.zero
      semigroup_add := hT.add
      isUnitary := fun y => ⟨(hU.isUnitary y).bijective, (hU.isUnitary y).norm_map⟩
      group_add := hU.add
      semigroup_mul_group := hU.commutes
      continuous_semigroup := hT.isStronglyContinuous
      continuous_group := hU.isStronglyContinuous }
  have hE := (hS _ _ _ hSC).1.2.1 (jointSpectralMeasure σ hσ.reflectionPositive)
    hJ.isJointSpectralMeasure
  have hK := (hG _ _ _ hSC).2.2.2.1
  have hH : hamiltonianOp σ hσ = YangMills.Construction.EnergyMomentum.Generators.hamiltonian
      (transferSemigroup σ hσ.reflectionPositive)
      (spatialTranslationRep σ hσ.reflectionPositive) := by
    simp only [hamiltonianOp, ReflectionPositivity.hamiltonian,
      YangMills.Construction.EnergyMomentum.Generators.hamiltonian, hE]
  refine ⟨?_, fun ψ => ?_⟩
  · rw [(hZ σ hσ).2, hE]
    exact hK.tendstoStrongly
  · rw [hH]
    exact (hK.tfae ψ).out 0 1
section Factorization
variable {σ : Tuple → ℝ} (hσ : ReconstructionData σ)
def GroundStateFactorizes : Prop :=
  ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
    (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
    ⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
      groundStateProjection σ hσ
        (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ =
      ((σ X * σ Y : ℝ) : ℂ)
variable {hσ}
theorem tendsto_timeCorrelation_inner (hl : CorrelationLimit σ hσ) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace) :
    Tendsto (timeCorrelation σ hX hY) atTop
      (𝓝 (⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
        groundStateProjection σ hσ
          (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (hl X Y hX hY)
  simp only [Function.comp_def, Complex.ofReal_re] at h
  exact h
theorem im_inner_groundState (hl : CorrelationLimit σ hσ) {X Y : Tuple}
    (hX : X ∈ tuplesSupportedIn upperHalfSpace) (hY : Y ∈ tuplesSupportedIn upperHalfSpace) :
    (⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
      groundStateProjection σ hσ
        (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (hl X Y hX hY)
  simp only [Function.comp_def, Complex.ofReal_im] at h
  exact tendsto_nhds_unique h tendsto_const_nhds
theorem clustersInTime_iff_factorizes (hl : CorrelationLimit σ hσ) :
    ClustersInTime σ ↔ GroundStateFactorizes hσ := by
  constructor
  · intro hc X Y hX hY
    exact tendsto_nhds_unique (hl X Y hX hY)
      ((Complex.continuous_ofReal.tendsto _).comp (hc X Y hX hY))
  · intro hp X Y hX hY
    have h := tendsto_timeCorrelation_inner hl hX hY
    rw [hp X Y hX hY, Complex.ofReal_re] at h
    exact h
theorem clustersInMean_iff_factorizes (hl : CorrelationLimit σ hσ)
    (hc : ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
      (hY : Y ∈ tuplesSupportedIn upperHalfSpace), Continuous (timeCorrelation σ hX hY)) :
    ClustersInMean σ ↔ GroundStateFactorizes hσ := by
  have hmean : ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
      (hY : Y ∈ tuplesSupportedIn upperHalfSpace),
      Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, timeCorrelation σ hX hY s.toNNReal) atTop
        (𝓝 (⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
          groundStateProjection σ hσ
            (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ).re) :=
    fun X Y hX hY => tendsto_average_of_tendsto
      (f := fun s : ℝ => timeCorrelation σ hX hY s.toNNReal)
      ((hc X Y hX hY).comp continuous_real_toNNReal)
      ((tendsto_timeCorrelation_inner hl hX hY).comp tendsto_real_toNNReal_atTop)
  constructor
  · intro ha X Y hX hY
    have h₁ := tendsto_nhds_unique (hmean X Y hX hY) (ha X Y hX hY)
    refine Complex.ext ?_ ?_
    · rw [h₁, Complex.ofReal_re]
    · rw [im_inner_groundState hl hX hY, Complex.ofReal_im]
  · intro hp X Y hX hY
    have h := hmean X Y hX hY
    rw [hp X Y hX hY, Complex.ofReal_re] at h
    exact h
theorem kernelIsVacuumRay_iff_factorizes
    (hP : IsProjOntoEnergyKernel σ hσ (groundStateProjection σ hσ))
    (hV : DenseTimeReconstruction.FormAndVacuumProps σ hσ.reflectionPositive)
    (hd : DenseRange (toReconstruction σ hσ.reflectionPositive)) :
    KernelIsVacuumRay σ hσ ↔ GroundStateFactorizes hσ := by
  constructor
  · intro hk X Y hX hY
    have hr : fixedSet (groundStateProjection σ hσ) =
        range fun c : ℂ => c • vacuum σ hσ.reflectionPositive := by
      rw [hP.fixedSet_eq]
      exact hk
    rw [apply_eq_inner_smul_of_fixedSet hP.isOrthProjection hV.norm_vacuum hr, inner_smul_right,
      hV.inner_vacuum_class, hV.inner_class_vacuum]
    push_cast
    ring
  · intro hp
    have hPQ : groundStateProjection σ hσ = (innerSL ℂ (vacuum σ hσ.reflectionPositive)).smulRight
        (vacuum σ hσ.reflectionPositive) := by
      refine ext_of_inner_tupleToComb _ hd _ _ fun X Y hX hY => ?_
      rw [hp X Y hX hY]
      change _ = ⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
        ⟪vacuum σ hσ.reflectionPositive,
          toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY)⟫_ℂ •
            vacuum σ hσ.reflectionPositive⟫_ℂ
      rw [inner_smul_right, hV.inner_vacuum_class, hV.inner_class_vacuum]
      push_cast
      ring
    have hA : ∀ ψ, groundStateProjection σ hσ ψ =
        ⟪vacuum σ hσ.reflectionPositive, ψ⟫_ℂ • vacuum σ hσ.reflectionPositive := by
      intro ψ
      rw [hPQ, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    unfold KernelIsVacuumRay
    rw [← hP.fixedSet_eq]
    exact fixedSet_eq_ray_of_apply hV.norm_vacuum hA
end Factorization
theorem vacuumClusteringHolds_of
    (hR : DenseTimeReconstruction.DenseTimeReconstructionHolds)
    (hC : FivePointCone.FivePointConeTheorem)
    (hE : GeneratorExponentials.GeneratorExponentialsHold)
    (hZ : GroundStateSpectral.GroundStateProjectionSpectral)
    (hG : YangMills.Construction.EnergyMomentum.Generators.GeneratorsTheorem)
    (hS : YangMills.Construction.EnergyMomentum.JointSpectral.JointSpectralMeasureTheorem)
    (hF : YangMills.Construction.BoundedOperators.BoundedOperatorFacts) :
    VacuumClusteringHolds := by
  intro σ hσ
  obtain ⟨hlim, hker⟩ := transferSemigroup_tendsto_and_kernel hR hS hG hZ σ hσ
  obtain ⟨-, hall⟩ := hR
  obtain ⟨hV, -, hc⟩ := hall σ hσ.reconstructionHypotheses
  obtain ⟨hT, hU, -, -, hJ⟩ := hc hσ.contractsOnDenseTimes
  have hP := (hZ σ hσ).1
  have hExp := hE σ hσ
  have hA : GroundStateIsStrongLimit σ hσ := by
    have e : heatOperator σ hσ = transferSemigroup σ hσ.reflectionPositive :=
      funext hExp.1
    unfold GroundStateIsStrongLimit
    rw [e]
    exact hlim
  have hL : CorrelationLimit σ hσ := by
    intro X Y hX hY
    have h₁ := (tendsto_const_nhds (x := toReconstruction σ hσ.reflectionPositive
      (tupleToComb X hX))).inner (𝕜 := ℂ)
      (hlim (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY)))
    exact h₁.congr fun t => inner_transferSemigroup_toReconstruction hT hX hY t
  have hcont : ∀ (X Y : Tuple) (hX : X ∈ tuplesSupportedIn upperHalfSpace)
      (hY : Y ∈ tuplesSupportedIn upperHalfSpace), Continuous (timeCorrelation σ hX hY) := by
    intro X Y hX hY
    have e : timeCorrelation σ hX hY = fun t =>
        (⟪toReconstruction σ hσ.reflectionPositive (tupleToComb X hX),
          transferSemigroup σ hσ.reflectionPositive t
            (toReconstruction σ hσ.reflectionPositive (tupleToComb Y hY))⟫_ℂ).re := by
      funext t
      rw [inner_transferSemigroup_toReconstruction hT hX hY t, Complex.ofReal_re]
    rw [e]
    exact Complex.continuous_re.comp (continuous_const.inner (hT.isStronglyContinuous _))
  have hd : DenseRange (toReconstruction σ hσ.reflectionPositive) :=
    (hF.2.1 _ (reflForm σ)
      (isPosSemidef_reflForm hσ.reflectionPositive)).2.2.1
  have h₁₃ : KernelIsVacuumRay σ hσ ↔ ClustersInTime σ :=
    (kernelIsVacuumRay_iff_factorizes hP hV hd).trans (clustersInTime_iff_factorizes hL).symm
  have h₃₄ : ClustersInTime σ ↔ ClustersInMean σ :=
    (clustersInTime_iff_factorizes hL).trans (clustersInMean_iff_factorizes hL hcont).symm
  have h₁₂ : KernelIsVacuumRay σ hσ → IsErgodic σ hσ := by
    intro hk ψ hψ
    have hm : ψ ∈ pmapKernel (hamiltonianOp σ hσ) := (hker ψ).2 hψ.1
    unfold KernelIsVacuumRay at hk
    rw [hk] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, hc.symm⟩
  refine ⟨hA, hL, h₁₃, h₃₄, fun h => h₁₂ (h₁₃.2 (h₃₄.2 h)), fun hdom => ?_⟩
  have hfix : ∀ ψ ∈ pmapKernel (hamiltonianOp σ hσ), ∀ v,
      spatialTranslationRep σ hσ.reflectionPositive v ψ = ψ := by
    intro ψ hψ v
    have hi : ∀ (i : Fin 3) (u : ℝ), spatialTranslationRep σ hσ.reflectionPositive
        (u • EuclideanSpace.single i (1 : ℝ)) ψ = ψ := fun i u => by
      rw [← hExp.2.2 i u]
      exact ((hC σ hσ i).2 (hdom i)).2 ψ hψ u
    have hv : v = (v 0 • EuclideanSpace.single 0 (1 : ℝ) + v 1 • EuclideanSpace.single 1 (1 : ℝ)) +
        v 2 • EuclideanSpace.single 2 (1 : ℝ) := by
      ext j
      fin_cases j <;> simp
    rw [hv, ← hU.add, ← hU.add]
    change spatialTranslationRep σ hσ.reflectionPositive _
      (spatialTranslationRep σ hσ.reflectionPositive _
        (spatialTranslationRep σ hσ.reflectionPositive _ ψ)) = ψ
    rw [hi, hi, hi]
  have hPk : ∀ ψ, groundStateProjection σ hσ ψ ∈ pmapKernel (hamiltonianOp σ hσ) := by
    intro ψ
    rw [← hP.fixedSet_eq]
    show groundStateProjection σ hσ (groundStateProjection σ hσ ψ) = groundStateProjection σ hσ ψ
    rw [← mul_apply_eq_comp, hP.isOrthProjection.idempotent]
  have hrange : GroundStateRange σ hσ :=
    { fixedSet_eq := by
        rw [hP.fixedSet_eq]
        ext ψ
        exact ⟨fun h => ⟨(hker ψ).1 h, hfix ψ h⟩, fun h => (hker ψ).2 h.1⟩
      vacuum_mem := by
        rw [hP.fixedSet_eq]
        exact hJ.vacuum_mem_hamiltonian_kernel
      rep_mul := fun v => ContinuousLinearMap.ext fun ψ => hfix _ (hPk ψ) v
      mul_rep := fun v => ContinuousLinearMap.ext fun ψ => by
        change groundStateProjection σ hσ (spatialTranslationRep σ hσ.reflectionPositive v ψ) =
          groundStateProjection σ hσ ψ
        refine ext_inner_left ℂ fun χ => ?_
        let li : ReconstructionSpace σ hσ.reflectionPositive →ₗᵢ[ℂ]
            ReconstructionSpace σ hσ.reflectionPositive :=
          ⟨(spatialTranslationRep σ hσ.reflectionPositive v).toLinearMap,
            (hU.isUnitary v).norm_map⟩
        have hi : ⟪spatialTranslationRep σ hσ.reflectionPositive v
            (groundStateProjection σ hσ χ),
            spatialTranslationRep σ hσ.reflectionPositive v ψ⟫_ℂ =
            ⟪groundStateProjection σ hσ χ, ψ⟫_ℂ :=
          li.inner_map_map _ _
        rw [hfix _ (hPk χ) v] at hi
        rw [hP.isOrthProjection.selfAdjoint χ, hP.isOrthProjection.selfAdjoint χ, hi] }
  refine ⟨hrange, ?_⟩
  tfae_have 1 ↔ 3 := h₁₃
  tfae_have 3 ↔ 4 := h₃₄
  tfae_have 1 → 2 := h₁₂
  tfae_have 2 → 1 := by
    intro he
    unfold KernelIsVacuumRay
    ext ψ
    constructor
    · intro hψ
      obtain ⟨c, hc⟩ := he ψ ⟨(hker ψ).1 hψ, hfix ψ hψ⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      refine (hker _).2 fun t => ?_
      simp only [map_smul, hT.fixes_vacuum t]
  tfae_finish
end YangMills.Construction.ReflectionPositivity.TimeClustering
