import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.ReferenceDensity
namespace YangMills.Construction.StepDensity
def InvariantAtAdmissibleParameters : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (t n : ℕ) [NeZero n], 64 ≤ n → ∀ W : TorusField n, IsCold T.threshold W →
    (∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion),
      stepDensityFamily T.coupling T.ρA T.lam T.side t n y (gaugeTransform g W) =
        stepDensityFamily T.coupling T.ρA T.lam T.side t n y W) ∧
    ∀ y u : TorusSite n, stepDensityFamily T.coupling T.ρA T.lam T.side t n y (TorusFields.translate u W) =
      stepDensityFamily T.coupling T.ρA T.lam T.side t n (y + u) W
end YangMills.Construction.StepDensity
end
