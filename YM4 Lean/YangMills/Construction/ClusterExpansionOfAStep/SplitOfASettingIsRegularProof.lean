import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import YangMills.Construction.ClusterExpansionOfAStep.StateDensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters
private theorem le_clusterRange_of_pow_le (N : ℕ) {x : ℝ} (hx : (N : ℝ) ^ 100 ≤ x) : N ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
private theorem measurable_logJacobianAt (hmean : MeasurableContourMeanStatement) {R : StepSetup} {n : ℕ}
    [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) : Measurable (s.logJacobianAt Y) := by
  classical
  have hgap : ∀ i : Fin 4, Measurable fun η : FreeCoords s.free =>
      logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s.field η) s.bases (Y, i)) := by
    intro i
    have hm := hmean R.params n s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Y, i)
      (fun q => ‖q‖) continuous_norm
    have hW : Measurable fun W : TorusField (n * R.params.side) => meanNorm R.params W s.bases (Y, i) := hm
    exact measurable_logPartitionGap.comp ((hW.comp (ChartSetting.measurable_field s)).const_mul _)
  have hlog : ∀ b : s.free, Measurable fun η : FreeCoords s.free =>
      Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) := by
    intro b
    exact Real.measurable_log.comp (measurable_haarLogDensity.comp
      (measurable_const.add (measurable_pi_apply b)))
  show Measurable fun η : FreeCoords s.free => s.logJacobian (s.field η) η Y
  unfold ChartSetting.logJacobian
  refine (Finset.measurable_fun_sum _ fun i _ => hgap i).add (Finset.measurable_fun_sum _ fun b _ => ?_)
  by_cases hb : bondBlock (R := R) b.1 = Y
  · simp only [if_pos hb]
    exact hlog b
  · simp only [if_neg hb]
    exact measurable_const
theorem densitySplitRegular_holds (hcost : CostHessianFloor) (hsize : LogJacobianBound)
    (hmean : MeasurableContourMeanStatement) (hdens : BlockDensitiesMeasurableBounded) :
    DensitySplitRegular := by
  obtain ⟨rt₀, hrt₀, hfloor⟩ := hcost
  refine ⟨rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨C₁, y₁, _, hfloor'⟩ := hfloor T hT hrt
  obtain ⟨C₂, y₂, _, hbound⟩ := hsize T hT
  set N : ℕ := 4 * T.n₀ + 2 ^ 16 + T.side + 2 with hN
  refine ⟨max (max (max T.floorMin y₁) (max y₂ ((N : ℝ) ^ 100))) 1, fun y hy R hR n _ hn s hs => ?_⟩
  have hy1 : T.floorMin ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hy))
  have hy2 : y₁ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hy))
  have hy3 : y₂ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hy4 : (N : ℝ) ^ 100 ≤ y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hy5 : (1 : ℝ) ≤ y := (le_max_right _ _).trans hy
  have hxy := hR.le_coupling
  have hadm : R.params.Admissible := hR.params_eq ▸ hT.fits y hy1
  have hEeq : R.params.E = T.E := by rw [hR.params_eq]; rfl
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hside : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hE : 1 ≤ R.params.E := by
    rw [hEeq]
    have := hT.B_ge
    unfold ParameterAssignment.E
    linarith
  have hx : 0 < R.coupling := by linarith
  have hr : N ≤ R.range := le_clusterRange_of_pow_le N (hy4.trans hxy)
  obtain ⟨hdensity, M₁, hM₁⟩ := hdens R n s hadm hE hx (by rw [hn₀]; omega) (by rw [hside]; omega)
    hR.isStep.1 (by rw [hn₀]; exact hn) hs
  have hdecay := hfloor' y hy2 R hR n hn s hs
  obtain ⟨U, hUo, hUb, hUc⟩ := hdecay.contDiffOn
  have hballs : ∀ η ∈ openBallsIn R s.free, s.InBalls η := fun η h b => (h b).le
  refine ⟨⟨U, hUo, hUb, hUc.of_le (by norm_num)⟩, fun Y => ?_, fun Y => ?_, ?_⟩
  · exact (measurable_logJacobianAt hmean s Y).indicator (measurableSet_openBallsIn (R := R))
  · obtain ⟨G, hG, hGe⟩ := hdensity Y
    have e : (openBallsIn R s.free).indicator (s.densitySplit.density Y) =
        (openBallsIn R s.free).indicator G :=
      Set.indicator_congr fun η h => (hGe η (hballs η h)).symm
    rw [e]
    exact hG.indicator (measurableSet_openBallsIn (R := R))
  · refine ⟨max M₁ (C₂ * Real.log R.coupling), fun η h Y => ⟨?_, ?_⟩⟩
    · exact (hbound y R hR.params_eq hR.anchorRadius_eq (hy3.trans hxy) n s Y η (hballs η h)).trans
        (le_max_right _ _)
    · exact (hM₁ η (hballs η h) Y).trans (le_max_left _ _)
end YangMills.Construction.ClusterExpansionOfAStep
end
