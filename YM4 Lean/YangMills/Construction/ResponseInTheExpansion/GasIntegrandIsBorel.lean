import YangMills.Construction.ClusterExpansionOfAStep.ImageAtAGroundIsTheSumOverTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.StepGas
def gasIntegrandMeasurableStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ F : YangMills.Construction.ClusterExpansionOfAStep.CaseFunctional R n,
      YangMills.Construction.ClusterExpansionOfAStep.IsCaseFunctional F →
      Measurable (G.gasIntegrand F)
end YangMills.Construction.WeightedResponses
end
