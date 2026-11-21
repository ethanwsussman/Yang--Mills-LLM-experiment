import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (observableSupNorm unitRegionObservables)
open ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def CubeReflectionNormProps : Prop :=
  ∀ (meas : unitPositiveClass) (r : ℕ+),
  (∀ A ∈ unitRegionObservables (cubeOfRadius r), ∀ B ∈ unitRegionObservables (cubeOfRadius r),
    cubeReflectionNorm meas r (A + B) ^ (1 / 2 : ℝ) ≤
      cubeReflectionNorm meas r A ^ (1 / 2 : ℝ) + cubeReflectionNorm meas r B ^ (1 / 2 : ℝ)) ∧
  (∀ c : ℂ, ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    cubeReflectionNorm meas r (c • A) ^ (1 / 2 : ℝ) =
      ‖c‖ * cubeReflectionNorm meas r A ^ (1 / 2 : ℝ)) ∧
  (∀ γ : axisReflectionGroup, ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    cubeReflectionNorm meas r ((axisReflectionGroup.toUnitLatticeSymmetry γ).actOn A) =
      cubeReflectionNorm meas r A) ∧
  ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    cubeReflectionNorm meas r A ≤ observableSupNorm A ^ 2
end YangMills.Construction.ReflectionPositivity.DirectionPictures
end
