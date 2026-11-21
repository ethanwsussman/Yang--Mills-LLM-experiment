import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import YangMills.Construction.RunningCouplingSlope.NumberOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def GaugeTotalMomentNearStepCoefficient : Prop :=
  ∃ (rt₀ C c : RenormalizationStepParameters.ChainParameters → ℝ), (∀ l, 0 < rt₀ l) ∧ (∀ l, 0 < C l) ∧ (∀ l, 0 < c l) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters → ∀ (t : ℕ) (b : ℝ),
      IsStepCoefficient T.coupling T.side t b →
        ∀ (n : ℕ) [NeZero n] (X : BlockAverages.imaginaryQuaternions), 64 ≤ n → ‖X‖ = 1 →
          |gaugeTotalMoment (SlopeCoefficient.stepGaugeTotal T.coupling T.ρA T.side t) n X - b| ≤
            C T.toChainParameters * Real.exp (-(c T.toChainParameters * n))
end YangMills.Construction.RunningCouplingSlope
end
