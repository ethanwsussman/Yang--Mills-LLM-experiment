import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def IsMeasurableFunctionOfLinksIn (S : Set AmbientSpace) (F : GaugeField a → ℂ) : Prop :=
  IsBoundedObservable F ∧ IsRegionMeasurable S F
def IsErgodicUnderShifts (μ : Measure (GaugeField a)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I → μ I = 0 ∨ μ I = 1
end InfiniteLattice
end YangMills.Construction
