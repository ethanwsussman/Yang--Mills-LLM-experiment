import YangMills.Construction.ReflectionPositivity.ReflectionGroupAndCubeReflectionSize
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField AmbientSpace axisStep shift
  halfSpaceLocalObservables observableSupNorm unitRegionObservables UnitLatticeSymmetry)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
def SignFlipsPreserveCube : Prop :=
  ∀ (ν : unitPositiveClass) (μ : Fin 4) (r : ℕ+),
  (∀ g : Equiv.Perm AmbientSpace, g ∈ axisReflectionGroup ↔
    ∃ ε : Fin 4 → ℤˣ, ⇑g = fun x i => ((ε i : ℤ) : ℝ) * x i) ∧
  Nat.card axisReflectionGroup = 16 ∧
  (∀ ε : Fin 4 → ℤˣ, ∃ s : UnitLatticeSymmetry, s.toFun = fun x i => ((ε i : ℤ) : ℝ) * x i) ∧
  (∀ γ : axisReflectionGroup,
    (axisReflectionGroup.toUnitLatticeSymmetry γ).setImage (cubeOfRadius r) = cubeOfRadius r) ∧
  (∀ γ : axisReflectionGroup, ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    (axisReflectionGroup.toUnitLatticeSymmetry γ).actOn A ∈
      unitRegionObservables (cubeOfRadius r)) ∧
  ∀ A ∈ unitRegionObservables (cubeOfRadius r),
    (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn A ∈
        unitRegionObservables {x | 0 ≤ x μ ∧ x μ ≤ 2 * (r : ℝ)} ∧
      (shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn A ∈ halfSpaceLocalObservables μ ∧
      ‖cubeVector ν μ r A‖ ≤ observableSupNorm A
end YangMills.Construction.ReflectionPositivity.DirectionPictures
