import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.InvariantEventsErgodicStatesAndExtremePoints
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAsHyperplanesAndToriOfAnyShape
import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.ReflectionPositivityDoesNotDependOnTheSide
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import YangMills.Construction.InfiniteLattice.StatesFunctionsOfTheBondsAndErgodicity
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries
open YangMills.Construction.LatticeConventions (NormalHyperplane)
open YangMills.Construction.LatticeConventions.NormalHyperplane (reflectSymmetry)
open YangMills.Construction.LatticeConventions.MirrorSideIndependence (reflectedPairing)
def periodicStates (a β : ℝ) : Set (Measure (GaugeField a)) :=
  {ν | IsPeriodicGibbs β ν}
def IsMotionInvariant {a : ℝ} (ν : Measure (GaugeField a)) : Prop :=
  ∀ r : latticeMotions a, IsSymmetricUnder ν (latticeMotionSymmetry r)
def IsReflectionPositiveAtAllMirrors {a : ℝ} (ν : Measure (GaugeField a)) : Prop :=
  ∀ (P : NormalHyperplane) (hP : P.IsLatticeMirror a),
    IsSymmetricUnder ν (reflectSymmetry hP) ∧
      (∀ F ∈ regionObservables a P.upperHalfSpace, reflectedPairing hP ν F ≥ 0) ∧
      ∀ F ∈ regionObservables a P.lowerHalfSpace, reflectedPairing hP ν F ≥ 0
def Statement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ β : ℝ, 0 < β →
    (∀ ν : Measure (GaugeField a), IsPeriodicGibbs β ν →
      IsMotionInvariant ν ∧ IsReflectionPositiveAtAllMirrors ν) ∧
    (periodicStates a β = {ν | IsGibbs β ν ∧ IsShiftInvariant ν}) ∧
    (periodicStates a β).Nonempty

end YangMills.Construction.InfiniteLattice.PeriodicGibbsSymmetries
end
