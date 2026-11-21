import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
instance instMeasurableSpaceGaugeFieldProbability (a : ℝ) :
    MeasurableSpace (GaugeFieldProbability a) :=
  borel (GaugeFieldProbability a)
instance instBorelSpaceGaugeFieldProbability (a : ℝ) :
    BorelSpace (GaugeFieldProbability a) :=
  ⟨rfl⟩
def periodicGibbsStates (L K : ℕ) (β : ℝ) :
    Set (GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | IsPeriodicGibbs β ν.1}
def IsWeakClusterPointOfLifts (L K : ℕ) (β : ℝ)
    (ν : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  ∀ O : Set (GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))), IsOpen O → ν ∈ O →
    ∀ ℓ₀ : ℝ, ∃ m : ℕ, 0 < m ∧ ℓ₀ ≤ PeriodicLattice.torusSide L m ∧
      ∃ ρ ∈ O, ρ.1 = liftedWilsonMeasure L m K β
def weakClusterPointsOfLifts (L K : ℕ) (β : ℝ) :
    Set (GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) :=
  {ν | IsWeakClusterPointOfLifts L K β ν}
variable {a : ℝ}
def IsInvariantDisintegration (ν : Measure (GaugeField a))
    (κ : GaugeField a → GaugeFieldProbability a) : Prop :=
  IsProbabilityMeasure ν ∧ IsShiftInvariant ν ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      Measurable[shiftInvariantSigma a] (fun U => (κ U).expect F) ∧
        (fun U => (κ U).expect F) =ᵐ[ν] condExpShiftInvariant ν F
def disintegrationImage (ν : Measure (GaugeField a))
    (κ : GaugeField a → GaugeFieldProbability a) : Measure (GaugeFieldProbability a) :=
  ν.map κ
end YangMills.Construction.InfiniteLattice
