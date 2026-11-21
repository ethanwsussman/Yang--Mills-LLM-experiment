import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open NormalFamilies
open GibbsAtFixedSpacing (continuousFns)
def mirrorReflectionPositiveStates (β : ℝ) (P : NormalLevelPair 1) :
    Set (Measure (GaugeField 1)) :=
  {ρ | ρ ∈ subgroupInvariantGibbsClass one_pos β (evenLattice.addSubgroupOf (latticeSubgroup 1)) ∧
    (∀ F ∈ continuousFns 1, stateEval ρ (P.reflectObservable F) = stateEval ρ F) ∧
    ∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
      0 ≤ stateEval ρ (P.conjReflectObservable F * F)}
end InfiniteLattice
end YangMills.Construction
