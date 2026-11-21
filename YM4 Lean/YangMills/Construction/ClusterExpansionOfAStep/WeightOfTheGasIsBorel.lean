import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StepGas
open RenormalizationStepParameters StepSettings TorusLumps TorusFields
def GasWeightMeasurable : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ S : StepSetup, S.OnParameters T y →
    S.nextCoupling ≤ 1.01 * S.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround S n), G.IsAdmissibleGround → Measurable G.weight
end YangMills.Construction.StepGas
end
