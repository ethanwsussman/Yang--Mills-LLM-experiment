import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
open YangMills.Construction.InfiniteLattice (regionObservables scaledCube)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
def CombinedBound : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    (∀ ν ∈ reflectionPositiveSet a,
      CoarseStepConditions ha ν ∧
      (∀ r : ℕ+, ReflectionSizeConditions ha ν r) ∧
      ∀ (r : ℕ+), ∀ A ∈ regionObservables a (scaledCube a r),
        ∀ B ∈ regionObservables a (scaledCube a r), ∀ μ : Fin 4,
          InverseSquareDecay ha ν μ r A B) ∧
    WeakClosed a ∧
    PeriodicGibbsReflectionPositive a
end YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
