import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepDensity
def AnalyticAtAdmissibleParameters : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (t n : ℕ) [NeZero n], 64 ≤ n →
    ∀ (y : TorusFields.TorusSite n) (W : TorusFields.TorusField n), TorusFields.IsCold (9 / 8 * T.threshold) W →
    ∀ (k : ℕ) (b : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ =>
        ReferenceDensity.stepDensityFamily T.coupling T.ρA T.lam T.side t n y (TorusFields.perturb b X τ W)) 0
end StepDensity
end YangMills.Construction
end
