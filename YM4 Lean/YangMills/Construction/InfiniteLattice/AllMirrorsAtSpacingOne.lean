import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open NormalFamilies
namespace InfiniteLattice
namespace UnitMeshReflectionPositivity
def Statement : Prop :=
  ∀ β : ℝ, 0 < β →
    (∀ ν : Measure (GaugeField 1), ν ∈ periodicGibbsClass one_pos β →
      (∀ P : NormalLevelPair 1,
        (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
          stateEval ν (P.reflectObservable F) = stateEval ν F) ∧
        ∀ F : GaugeField 1 → ℂ,
          (F ∈ halfSpaceObservables 1 P.normal P.level 1 ∨
            F ∈ halfSpaceObservables 1 P.normal P.level (-1)) →
          0 ≤ stateEval ν (P.conjReflectObservable F * F)) ∧
      IsShiftInvariant ν ∧
      ∀ g : LatticeSymmetry 1, (∃ w ∈ hyperoctahedralLinearGroup, g.toFun = ⇑w) → IsSymmetricUnder ν g) ∧
    (∀ R : AmbientSpace →ₗ[ℝ] AmbientSpace,
      IsLatticeLinearIsometry 1 R ↔ ∃ w ∈ hyperoctahedralLinearGroup, ⇑w = ⇑R) ∧
    periodicGibbsClass one_pos β = subgroupInvariantGibbsClass one_pos β ⊤
end UnitMeshReflectionPositivity
end InfiniteLattice
end YangMills.Construction
