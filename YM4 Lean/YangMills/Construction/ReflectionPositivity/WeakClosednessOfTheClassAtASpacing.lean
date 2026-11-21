import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open CoarseStepsInverseSquare (WeakClosed)
def WeakClosedEveryMesh : Prop :=
  ∀ (a : ℝ), 0 < a → WeakClosed a
end YangMills.Construction.ReflectionPositivity.DirectionPictures
