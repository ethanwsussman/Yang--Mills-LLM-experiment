import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MinimizerDensityMomentDecay : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ l, 0 < rt₀ l) ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (y : ℝ) (R : StepSettings.StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      R.IsSymmetricWeight →
      ∀ (n : ℕ) [NeZero n] (X : BlockAverages.imaginaryQuaternions), T.n₀ ≤ n → ‖X‖ = 1 →
        |gaugeTotalMoment (densityAtMinimizer R) n X| ≤ C * Real.exp (-(c * n))
end YangMills.Construction.RunningCouplingSlope
end
