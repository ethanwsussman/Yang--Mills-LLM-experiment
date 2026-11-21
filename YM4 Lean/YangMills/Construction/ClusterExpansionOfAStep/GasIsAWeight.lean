import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusLumps StepSettings StepGas RenormalizationStepParameters Dobrushin
namespace StepGas
variable {R : StepSetup} {n : ℕ}
def GasGround.spinActivity [NeZero n] (G : GasGround R n) (c : ℝ) (i : G.GasSpin) : ℝ :=
  clusterWeight R.params.side c R.coupling R.range i.1
end StepGas
namespace ClusterExpansionOfAStep
def GasIsActivityBounded : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ off : G.GasSpin → Prop,
        G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight (G.spinActivity T.gasRate)
end ClusterExpansionOfAStep
end YangMills.Construction
end
