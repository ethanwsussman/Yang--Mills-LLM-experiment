import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open LatticeAtSpacing (reflectionPositiveSet)
def CoarseStepsEveryMesh : Prop :=
  ∀ (a : ℝ) (ha : 0 < a), ∀ ν ∈ reflectionPositiveSet a,
    CoarseStepsInverseSquare.CoarseStepConditions ha ν
end YangMills.Construction.ReflectionPositivity.DirectionPictures
