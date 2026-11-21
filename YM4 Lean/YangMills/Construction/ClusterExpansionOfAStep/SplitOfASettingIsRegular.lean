import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters StepSettings
def DensitySplitRegular : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
      ∀ s : ChartSetting R n, s.IsAdmissible → s.densitySplit.IsRegular
end YangMills.Construction.ClusterExpansionOfAStep
end
