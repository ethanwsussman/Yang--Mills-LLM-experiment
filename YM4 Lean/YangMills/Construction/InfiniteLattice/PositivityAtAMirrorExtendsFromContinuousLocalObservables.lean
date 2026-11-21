import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open scoped ComplexOrder
namespace InfiniteLattice
open NormalFamilies
def ReflectionPositivityExtendsFromLocal : Prop :=
  ∀ (P : NormalLevelPair 1) (ν : Measure (GaugeField 1)), IsProbabilityMeasure ν →
    IsSymmetricUnder ν P.reflectSymmetry →
    (∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
      0 ≤ stateEval ν (P.conjReflectObservable F * F)) →
    ∀ F, (F ∈ halfSpaceObservables 1 P.normal P.level 1 ∨
        F ∈ halfSpaceObservables 1 P.normal P.level (-1)) →
      0 ≤ stateEval ν (P.conjReflectObservable F * F)
end InfiniteLattice
end YangMills.Construction
end
