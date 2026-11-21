import YangMills.Construction.Conventions.SpatialRotationDefs
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ComplexMeasureVanishing
open RotationNotation
def Statement : Prop :=
  ∀ (Y : SpaceTag) (ν : ComplexMeasure Y.Pts),
    (∀ φ : Y.Pts → ℝ, Continuous φ → HasCompactSupport φ →
      integralC ν (fun y => (φ y : ℂ)) = 0) →
    ν = 0
end YangMills.Construction.ComplexMeasureVanishing
end
