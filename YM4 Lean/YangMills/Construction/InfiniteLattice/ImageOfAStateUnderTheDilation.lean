import YangMills.Construction.InfiniteLattice.DilationOntoTheUnitLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def dilatedState (ha : 0 < a) (μ : Measure (GaugeField a)) : Measure (GaugeField 1) :=
  scaledState (inv_pos.2 ha) (one_eq_inv_mul_spacing ha) μ
theorem dilatedState_eq_map (ha : 0 < a) (μ : Measure (GaugeField a)) :
    dilatedState ha μ = μ.map (fieldRescale ha) := rfl
instance (ha : 0 < a) (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (dilatedState ha μ) :=
  inferInstanceAs (IsProbabilityMeasure (scaledState (inv_pos.2 ha) (one_eq_inv_mul_spacing ha) μ))
end YangMills.Construction.InfiniteLattice
