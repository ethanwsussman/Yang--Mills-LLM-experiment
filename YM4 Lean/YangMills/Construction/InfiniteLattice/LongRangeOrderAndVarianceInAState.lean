import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def longRangeOrderParameter (μ : Measure (GaugeField a)) (F : GaugeField a → ℂ) : ℂ :=
  plateauPairing μ F F - ((‖∫ U, F U ∂μ‖ ^ 2 : ℝ) : ℂ)
theorem longRangeOrderParameter_eq_plateauVariance (μ : Measure (GaugeField a))
    (F : GaugeField a → ℂ) : longRangeOrderParameter μ F = plateauVariance μ F :=
  rfl
def stateVariance (μ : Measure (GaugeField a)) (F : GaugeField a → ℂ) : ℝ :=
  ∫ U, ‖F U - ∫ V, F V ∂μ‖ ^ 2 ∂μ
end YangMills.Construction.InfiniteLattice
