import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open RenormalizationStepParameters StepSettings BlockAverages
def ChartDensitySupportedOnLiveStates : Prop :=
  ∀ P : ParameterAssignment, P.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters P y →
    ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n), R.params.n₀ ≤ n → s.IsAdmissible → ∀ η, chartDensity s η ≠ 0 →
      IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling
end YangMills.Construction.WeightedResponses
end
