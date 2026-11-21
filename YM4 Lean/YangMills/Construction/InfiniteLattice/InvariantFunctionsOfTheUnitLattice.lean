import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def axisMultiples (μ : Fin 4) : Set (LatticePoint 1) := {v | ∃ k : ℤ, v = k • axisStep 1 μ}
inductive ShiftPair : Type
  | allShifts : ShiftPair
  | axis (μ : Fin 4) : ShiftPair
@[reducible] def ShiftPair.sigma : ShiftPair → MeasurableSpace (GaugeField 1)
  | .allShifts => shiftInvariantSigma 1
  | .axis μ => axisShiftInvariantSigma μ
def ShiftPair.shifts : ShiftPair → Set (LatticePoint 1)
  | .allShifts => Set.univ
  | .axis μ => axisMultiples μ
theorem axisShiftInvariantSigma_le_borel (μ : Fin 4) :
    axisShiftInvariantSigma μ ≤ (inferInstance : MeasurableSpace (GaugeField 1)) :=
  fun _ hs => hs.1
namespace ShiftInvariantFunctions
def MeasurableIffShiftInvariant (p : ShiftPair) : Prop :=
  ∀ f : GaugeField 1 → ℂ, Measurable f →
    (Measurable[p.sigma] f ↔ ∀ v ∈ p.shifts, (shift v).actOn f = f)
def AEInvariantHasMeasurableModification (p : ShiftPair)
    (ν : Measure (GaugeField 1)) : Prop :=
  ∀ f : GaugeField 1 → ℂ, Measurable f →
    (∀ v ∈ p.shifts, (shift v).actOn f =ᵐ[ν] f) →
    ∃ g : GaugeField 1 → ℂ, Measurable[p.sigma] g ∧ g =ᵐ[ν] f
def InvariantL2ApproxByHalfSpace (μ : Fin 4)
    (ν : Measure (GaugeField 1)) : Prop :=
  IsSymmetricUnder ν (shift (axisStep 1 μ)) →
    ∀ f : Lp ℂ 2 ν,
      f ∈ FormHilbert.subFieldL2 ν (axisShiftInvariantSigma μ)
        (axisShiftInvariantSigma_le_borel μ) →
      ∀ ε : ℝ, 0 < ε →
        ∃ g : GaugeField 1 → ℂ, Continuous g ∧ g ∈ halfSpaceLocalObservables μ ∧
          ∃ hg : MemLp g 2 ν, ‖f - hg.toLp g‖ ≤ ε
def InvariantFunctionsTheorem : Prop :=
  (∀ p : ShiftPair, MeasurableIffShiftInvariant p) ∧
    ∀ (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν],
      (∀ p : ShiftPair, AEInvariantHasMeasurableModification p ν) ∧
      ∀ μ : Fin 4, InvariantL2ApproxByHalfSpace μ ν
end ShiftInvariantFunctions
end YangMills.Construction.InfiniteLattice
end
