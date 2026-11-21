import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
  (ReflectionSizeConditions)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
def ReflectionSizeBoundsAtMesh : Prop :=
  ∀ (a : ℝ) (ha : 0 < a), ∀ ν ∈ reflectionPositiveSet a, ∀ r : ℕ+, ReflectionSizeConditions ha ν r
end YangMills.Construction.ReflectionPositivity.DirectionPictures
