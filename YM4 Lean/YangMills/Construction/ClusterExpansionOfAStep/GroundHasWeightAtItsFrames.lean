import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfAGround
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages RenormalizationStepParameters StepSettings StepGas
namespace StepGas
def GroundWeightAtEmpty : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      G.HasWeightAt GasFamily.empty 0
end StepGas
end YangMills.Construction
end
