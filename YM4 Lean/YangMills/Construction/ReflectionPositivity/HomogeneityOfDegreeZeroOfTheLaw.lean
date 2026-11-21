import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SpacingInvariance
open YangMills.Construction.InfiniteLattice (regionObservables scaledCube)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
  (ScaleInvariance)
def Holds : Prop :=
  ∀ (a : ℝ) (ha : 0 < a), ∀ ν ∈ reflectionPositiveSet a, ∀ (r : ℕ+),
    ∀ A ∈ regionObservables a (scaledCube a r), ∀ B ∈ regionObservables a (scaledCube a r),
      ∀ μ : Fin 4, ScaleInvariance ha ν μ r A B
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SpacingInvariance
