import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def IsShiftErgodic (ν : Measure (GaugeField a)) : Prop :=
  IsProbabilityMeasure ν ∧ IsShiftInvariant ν ∧
    ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I → ν I = 0 ∨ ν I = 1
def extremalPhases (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsPeriodicGibbs β ν ∧ IsShiftInvariant ν ∧ IsShiftErgodic ν}
def plateauPairing (ν : Measure (GaugeField a)) (A B : GaugeField a → ℂ) : ℂ :=
  ∫ U, conj (condExpShiftInvariant ν A U) * condExpShiftInvariant ν B U ∂ν
end InfiniteLattice
end YangMills.Construction
end
