import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PlateauVarianceFormula : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ],
    IsShiftInvariant μ → ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      ∫ U, condExpShiftInvariant μ F U ∂μ = ∫ U, F U ∂μ ∧
        plateauVariance μ F =
          ((∫ U, ‖condExpShiftInvariant μ F U - ∫ V, F V ∂μ‖ ^ 2 ∂μ : ℝ) : ℂ) ∧
        plateauVariance μ F =
          ((∫ U, ‖condExpShiftInvariant μ F U - ∫ V, condExpShiftInvariant μ F V ∂μ‖ ^ 2 ∂μ : ℝ) :
            ℂ) ∧
        0 ≤ plateauVariance μ F
end YangMills.Construction.InfiniteLattice
