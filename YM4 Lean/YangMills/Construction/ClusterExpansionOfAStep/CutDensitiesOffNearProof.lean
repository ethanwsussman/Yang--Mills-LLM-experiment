import YangMills.Construction.ClusterExpansionOfAStep.CutDensitiesOffNear
import YangMills.Construction.ClusterExpansionOfAStep.CutOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.OffNearDensitiesMoveLittle
import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames Restriction StepSettings TorusFields RenormalizationStepParameters
  TorusLumps Interpolation
namespace AwayFromNear
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem extendByZero_eq_restrictTo (s : ChartSetting R n) (N : Finset (TorusSite n)) (η : FreeCoords s.free) :
    s.extendByZero N (fun b => η b.1) = s.restrictTo (s.freeNear N) η := by
  classical
  funext b
  by_cases h : b ∈ s.freeNear N
  · simp only [ChartSetting.extendByZero, ChartSetting.restrictTo]
    rw [dif_pos h, if_pos h]
  · simp only [ChartSetting.extendByZero, ChartSetting.restrictTo]
    rw [dif_neg h, if_neg h]
theorem not_mem_freeNear_of_mem_freeBondsAt (s : ChartSetting R n) {N : Finset (TorusSite n)} {Y : TorusSite n}
    (hY : Y ∉ N) : ∀ b ∈ freeBondsAt s.free Y, b ∉ s.freeNear N := by
  classical
  intro b hb hm
  have h1 : bondBlock (R := R) b.1 = Y := (Finset.mem_filter.mp hb).2
  have h2 : bondBlock (R := R) b.1 ∈ N := (Finset.mem_filter.mp hm).2
  exact hY (h1 ▸ h2)
end AwayFromNear
open AwayFromNear in
set_option maxHeartbeats 1600000 in
theorem cutActivitiesAwayFromNear_of (hcore : LogIntegralExpInterpolationStatement)
    (hreg : DensitySplitRegular) (hoff : farBlockDensityVariationBound) :
    CutActivitiesAwayFromNear := by
  classical
  obtain ⟨rt₀, hrt₀, hreg⟩ := hreg
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨y₁, hy₁⟩ := hreg T hT hrt
  obtain ⟨CE, y₂, hCE, hoff⟩ := hoff T hT
  refine ⟨2 * CE, max y₁ y₂, by positivity, fun y hy R hR n _ hn s c hs hc 𝒦 h𝒦 => ?_⟩
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans hy
  have hy2 : y₂ ≤ y := (le_max_right _ _).trans hy
  have hρe : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hR.params_eq]
    rfl
  have hρ : 0 < R.ballRadius := by
    rw [hρe]
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρe, hR.barrierFn_eq]
    exact hT.cut
  have hsr := hy₁ y hy1 R hR n hn s hs
  generalize hN : blocksNear R.params.side R.range (𝒦.biUnion id) = N
  have hoffN := hoff y hy2 R hR n hn s c hs hc 𝒦 h𝒦
  rw [hN] at hoffN
  set X := s.freeNear N with hX
  set D := s.restrictedSplit T.lam X with hD
  have hDreg : D.IsRegular := restrictedSplit_isRegular s T.lam X hρ hsr
  set Bd : ℝ := CE * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) with hBd
  let μ := volume.restrict (openBallsIn R s.free)
  have hjB : ∀ Y, AEBounded μ fun η => D.logJacobian Y 0 - D.logJacobian Y η := fun Y =>
    (AEBounded.const _).sub (aeBounded_logJacobian hDreg Y)
  have hpB : ∀ Y, AEBounded μ fun η => D.density Y η - s.blockDensityAt Y 0 := fun Y =>
    (aeBounded_density hDreg Y).sub (AEBounded.const _)
  have hball : ∀ η ∈ openBallsIn R s.free, s.InBalls (s.extendByZero N fun b => η b.1) := by
    intro η hη b
    rw [extendByZero_eq_restrictTo]
    exact (restrictTo_mem_openBallsIn s X hρ hη b).le
  have hbj : ∀ η ∈ openBallsIn R s.free,
      |∑ Y ∈ Finset.univ \ N, (D.logJacobian Y 0 - D.logJacobian Y η)| ≤ Bd := by
    intro η hη
    have h1 := hoffN (fun b => η b.1) (hball η hη)
    rw [extendByZero_eq_restrictTo] at h1
    have h2 : 0 ≤ ∑ Y ∈ Finset.univ \ N,
        |s.blockDensity (s.field (s.restrictTo X η)) Y - s.blockDensity (s.field 0) Y| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 : |∑ Y ∈ Finset.univ \ N, (D.logJacobian Y 0 - D.logJacobian Y η)| ≤
        ∑ Y ∈ Finset.univ \ N,
          |s.logJacobian (s.field (s.restrictTo X η)) (s.restrictTo X η) Y - s.logJacobian (s.field 0) 0 Y| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun Y _ => ?_)
      rw [abs_sub_comm]
      rw [restrictedSplit_logJacobian_zero]
      exact le_rfl
    linarith only [h1, h2, h3]
  have hbp : ∀ η ∈ openBallsIn R s.free,
      |∑ Y ∈ Finset.univ \ N, (D.density Y η - s.blockDensityAt Y 0)| ≤ Bd := by
    intro η hη
    have h1 := hoffN (fun b => η b.1) (hball η hη)
    rw [extendByZero_eq_restrictTo] at h1
    have h2 : 0 ≤ ∑ Y ∈ Finset.univ \ N,
        |s.logJacobian (s.field (s.restrictTo X η)) (s.restrictTo X η) Y - s.logJacobian (s.field 0) 0 Y| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h3 : |∑ Y ∈ Finset.univ \ N, (D.density Y η - s.blockDensityAt Y 0)| ≤
        ∑ Y ∈ Finset.univ \ N, |s.blockDensity (s.field (s.restrictTo X η)) Y - s.blockDensity (s.field 0) Y| :=
      Finset.abs_sum_le_sum_abs _ _
    linarith only [h1, h2, h3]
  have ht := abs_sum_integral_weightedMean_interpolatedDensity_le hcore hρ hp hDreg T.lam (Finset.univ \ N) hjB hbj
  have hn' := abs_sum_integral_weightedMean_perturbedDensity_le hcore hρ hp hDreg (Finset.univ \ N) hpB hbp
  have hkey : ∀ Y ∈ Finset.univ \ N, D.activity T.lam Y +
      (R.coupling * s.blockCostAt Y 0 - s.blockDensityAt Y 0 - s.logJacobianAt Y 0) -
      R.gaussianLogMass T.lam * (freeBondsAt s.free Y).card =
      -(∫ τ in (0 : ℝ)..1, weightedMean (D.interpolatedDensity T.lam τ)
          fun η => D.logJacobian Y 0 - D.logJacobian Y η) +
      ∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) fun η => D.density Y η - s.blockDensityAt Y 0 := by
    intro Y hY
    have hYN : Y ∉ N := by simpa using hY
    have e1 : (fun η => D.interaction Y η - gaussianPart T.lam Y η) =
        fun η => D.logJacobian Y 0 - D.logJacobian Y η := by
      funext η
      exact restrictedSplit_interaction_sub_gaussianPart s T.lam (not_mem_freeNear_of_mem_freeBondsAt s hYN) η
    have e2 : ∀ ν, weightedMean (D.perturbedDensity ν) (D.density Y) =
        weightedMean (D.perturbedDensity ν) (fun η => D.density Y η - s.blockDensityAt Y 0) +
          s.blockDensityAt Y 0 := fun ν =>
      (weightedMean_perturbedDensity_sub_const_add hcore hρ hp hDreg ν (aeBounded_density hDreg Y)
        (s.blockDensityAt Y 0)).symm ▸ rfl
    have e3 : ∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) (D.density Y) =
        (∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) fun η => D.density Y η - s.blockDensityAt Y 0) +
          s.blockDensityAt Y 0 := by
      simp_rw [e2]
      rw [intervalIntegral.integral_add
        ((continuous_weightedMean_perturbedDensity hcore hρ hp hDreg (hpB Y)).intervalIntegrable _ _)
        intervalIntegrable_const]
      simp
    unfold BlockDensitySplit.activity
    rw [e1, e3, restrictedSplit_cost_zero, restrictedSplit_logJacobian_zero]
    ring
  rw [Finset.sum_congr rfl hkey, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h2 : (2 * CE) * (R.range : ℝ) ^ 4 * Real.log R.coupling * (N.card : ℝ) = Bd + Bd := by
    rw [hBd]
    ring
  rw [h2]
  refine (abs_add_le _ _).trans (add_le_add ?_ hn')
  rw [abs_neg]
  exact ht
end YangMills.Construction.ClusterExpansionOfAStep
end
