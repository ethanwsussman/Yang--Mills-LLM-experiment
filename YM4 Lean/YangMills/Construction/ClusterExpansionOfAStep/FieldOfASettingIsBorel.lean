import YangMills.Construction.ClusterExpansionOfAStep.CostAndWideEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts StepSettings
theorem continuous_toImaginary : Continuous toImaginary := by apply _root_.YangMills.Construction.StepCostLocality.continuous_toImaginary <;> assumption
theorem ChartSetting.measurable_field {R : StepSetup} {n : ℕ} (s : StepSettings.ChartSetting R n) :
    Measurable s.field := by
  classical
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => ?_
  unfold StepSettings.ChartSetting.field
  by_cases h : (x, i) ∈ s.free
  · simp only [dif_pos h]
    have hc : Continuous fun η : FreeCoords s.free =>
        chartLink s x i (s.frame (x, i) + toImaginary (η ⟨(x, i), h⟩)) := by
      unfold chartLink
      have h1 : Continuous fun η : FreeCoords s.free => expUnit (s.frame (x, i) + toImaginary (η ⟨(x, i), h⟩)) :=
        continuous_expUnit.comp (continuous_const.add (continuous_toImaginary.comp (continuous_apply _)))
      by_cases hc : IsCrossingBond (F := stepBlockFrame R.params.side n)
          (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
      · simp only [if_pos hc]
        exact (continuous_const.mul (h1.mul continuous_const)).mul continuous_const
      · simp only [if_neg hc]
        exact (continuous_const.mul h1).mul continuous_const
    exact hc.measurable
  · simp only [dif_neg h]
    exact measurable_const
theorem continuous_partitionFn : Continuous partitionFn := by
  have hf : Continuous (Function.uncurry fun (s : ℝ) (g : UnitQuaternion) =>
      Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re)) := by
    have h1 : Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
      Quaternion.continuous_re.comp continuous_subtype_val
    refine Real.continuous_exp.comp ?_
    exact continuous_fst.mul (h1.comp continuous_snd)
  have := continuous_parametric_integral_of_continuous (μ := haarUnit) hf (isCompact_univ (X := UnitQuaternion))
  have e : (fun x : ℝ => ∫ y in Set.univ, Real.exp (x * ((y : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit) =
      partitionFn := by
    funext s
    simp only [Measure.restrict_univ]
    rfl
  rw [← e]
  exact this
theorem measurable_logPartitionGap : Measurable logPartitionGap := by
  unfold logPartitionGap
  exact measurable_id.sub (Real.measurable_log.comp continuous_partitionFn.measurable)
end YangMills.Construction.ClusterExpansionOfAStep
end
