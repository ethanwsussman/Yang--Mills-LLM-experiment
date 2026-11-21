import YangMills.Construction.RunningCouplingSlope.TestOfATotal
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps TorusFields RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope
def SmallDensityHessianBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧
    ∀ (y e : ℝ) (g : LocalDensity), T.floorMin ≤ y → 0 ≤ e →
    IsSmallDensity (T.stepParameters y) e g → ∀ n : ℕ, T.n₀ ≤ n →
      IsGaugeFunctionNear (centeredDensityTotal g) n ∧
        HessianBoundedBy (centeredDensityTotal g) n (C * e) θ
end RunningCouplingSlope
end YangMills.Construction
end
