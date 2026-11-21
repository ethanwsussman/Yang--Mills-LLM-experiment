import YangMills.Construction.ReflectionPositivity.CoarseStepsAndTheInverseSquareLaw
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SpacingDecayAndLaw
open YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
  (CubeVectorDecay SeparatedCubeBound UnconjugatedBound LargeDistanceBound)
open YangMills.Construction.InfiniteLattice (regionObservables scaledCube plateauPairing)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
  (reflectionPositiveSet IsErgodicState)
def Statement : Prop :=
  ∀ (a : ℝ) (ha : 0 < a), ∀ ν ∈ reflectionPositiveSet a, ∀ r : ℕ+,
    ∀ A ∈ regionObservables a (scaledCube a r), ∀ B ∈ regionObservables a (scaledCube a r),
      ∀ μ : Fin 4,
        CubeVectorDecay ha ν μ r A ∧
        SeparatedCubeBound ha ν r A B ∧
        UnconjugatedBound ha ν r A B ∧
        LargeDistanceBound ha ν r A B ∧
        (IsErgodicState ν → plateauPairing ν.1 A B = conj (ν.integral A) * ν.integral B)
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SpacingDecayAndLaw
