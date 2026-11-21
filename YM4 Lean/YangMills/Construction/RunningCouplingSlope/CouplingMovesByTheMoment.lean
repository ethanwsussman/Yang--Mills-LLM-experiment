import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusLumps YangMills.Construction.StepSettings
def CouplingShiftEqualsGaugeMoment : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ l, 0 < rt₀ l) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C₁ : ℝ, C₀ ≤ C₁ →
    ∃ C ys : ℝ, 0 < C ∧ ∀ (y : ℝ) (R : StepSetup) (x' : ℝ) (f' : LocalDensity), T.floorMin ≤ y →
      R.OnParameters T y → R.IsSymmetricWeight → ys ≤ R.coupling → |x' - R.coupling| ≤ 2 * T.B →
      ColdExpansion R.params (R.depth + 1) x' (kernelImage R.params R.coupling R.functional) f' →
      ∀ (n : ℕ) [NeZero n] (X : imaginaryQuaternions), n = stepTorusSide T.n₀ C₁ R.coupling → ‖X‖ = 1 →
        |R.coupling - x' - gaugeTotalMoment (laplaceRemainder R) n X| ≤ C / R.coupling
end YangMills.Construction.RunningCouplingSlope
end
