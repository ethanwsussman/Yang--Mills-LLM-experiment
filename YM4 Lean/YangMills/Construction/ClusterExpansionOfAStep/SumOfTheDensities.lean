import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings TorusFields
def LogIntegralEqSumActivity : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ s : ChartSetting R n, s.IsAdmissible →
        Real.log (∫ η, s.cutoffProduct η * Real.exp (-s.potential η)) = ∑ Y : TorusSite n, s.blockActivity T.lam Y
end YangMills.Construction.ClusterExpansionOfAStep
end
