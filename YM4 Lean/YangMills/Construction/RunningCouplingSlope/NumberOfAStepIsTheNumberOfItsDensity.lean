import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParameters
import YangMills.Construction.RunningCouplingSlope.NumberOfAStep
import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.RenormalizationStepParameters
namespace YangMills.Construction.RunningCouplingSlope
def StepCoefficientEqualsDensityValue : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ t : ℕ, ∃ b : ℝ, IsStepCoefficient T.coupling T.side t b ∧
    YangMills.Construction.FamilyNorms.HasUnitPlaneValue (paramStepDensity T t) b
end YangMills.Construction.RunningCouplingSlope
end
