import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def DensityDerivativesDecay : Prop :=
  ∃ c C : RenormalizationStepParameters.ChainParameters → ℝ, (∀ l, 0 < c l) ∧ (∀ l, 0 < C l) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible →
    ∀ (t n : ℕ) [NeZero n], 64 ≤ n → ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n),
      TorusFields.IsCold (9 / 8 * T.threshold) W →
      ∀ (k : ℕ) (b : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
        1 ≤ k → k ≤ 3 → BlockAverages.AreUnitVectors X →
        |TorusFields.mixedDeriv
            (ReferenceDensity.stepDensityFamily T.coupling T.ρA T.lam T.side t n y) W b X| ≤
          C T.toChainParameters * Real.exp (-(c T.toChainParameters * TorusFields.supportDiam y b))
end RunningCouplingSlope
end YangMills.Construction
end
