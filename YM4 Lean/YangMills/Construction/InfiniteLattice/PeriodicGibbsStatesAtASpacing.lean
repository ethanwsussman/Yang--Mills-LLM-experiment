import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAsHyperplanesAndToriOfAnyShape
import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsAtSpacing
open YangMills.Construction.LatticeConventions YangMills.Construction.LatticeConventions.NormalHyperplane
variable {a : ℝ}
def mirrorPairing {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
    (F : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conjFun ((reflectSymmetry hQ).actOn F) U * F U
def HasSymmetriesAndReflectionPositivity (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] : Prop :=
  (∀ v : LatticePoint a, IsSymmetricUnder ν (shift v)) ∧
    (∀ g : LatticeSymmetry a, ∀ w ∈ hyperoctahedralLinearGroup, (∀ x, g.toFun x = w x) →
      IsSymmetricUnder ν g) ∧
    ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a),
      IsSymmetricUnder ν (reflectSymmetry hQ) ∧
        (∀ F ∈ regionObservables a Q.upperHalfSpace, 0 ≤ stateEval ν (mirrorPairing hQ F)) ∧
        (∀ F ∈ regionObservables a Q.lowerHalfSpace, 0 ≤ stateEval ν (mirrorPairing hQ F)) ∧
        IsReflectionPositiveAcrossMirror hQ ν
def PeriodicGibbsSymmetric (a β : ℝ) : Prop :=
  ∀ (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν], IsPeriodicGibbs β ν →
    HasSymmetriesAndReflectionPositivity ν
def CubicPeriodsAdmissible (a : ℝ) : Prop :=
  ∀ s : ℕ → ℤ, (∀ i, 1 ≤ i → 3 ≤ s i) → Tendsto s atTop atTop →
    ∃ Γ : ℕ → PeriodSublattice a,
      (∀ i, 1 ≤ i → (Γ i).periods = cubicSublattice a ((s i : ℝ) * a)) ∧
        MinNonzeroNormTendsToInfinity Γ
def TorusLimitsAreShiftInvariantGibbs (a β : ℝ) : Prop :=
  ∀ Γ : ℕ → PeriodSublattice a, MinNonzeroNormTendsToInfinity Γ →
    ∀ (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν],
      IsWeakClusterPoint (fun i => (Γ i).liftedGibbsMeasure β) ν →
        IsGibbs β ν ∧ IsShiftInvariant ν ∧ IsPeriodicGibbs β ν ∧
          HasSymmetriesAndReflectionPositivity ν
def PeriodicGibbsSetCharacterization (a β : ℝ) : Prop :=
  {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν} =
      {ν | IsGibbs β ν ∧ IsShiftInvariant ν} ∧
    {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν}.Nonempty ∧
    Convex ℝ≥0 {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν} ∧
    IsWeakCompact {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν}
def Statement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ β : ℝ, 0 < β →
    PeriodicGibbsSymmetric a β ∧
      CubicPeriodsAdmissible a ∧
      TorusLimitsAreShiftInvariantGibbs a β ∧
      PeriodicGibbsSetCharacterization a β
end YangMills.Construction.InfiniteLattice.PeriodicGibbsAtSpacing
end
