import YangMills.Construction.InfiniteLattice.ErgodicPhases
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def plateauForm (μ : Measure (GaugeField a)) (A B : GaugeField a → ℂ) : ℂ :=
  ∫ V, conj (condExpShiftInvariant μ A V) * condExpShiftInvariant μ B V ∂μ
def plateauVariance (μ : Measure (GaugeField a)) (A : GaugeField a → ℂ) : ℂ :=
  plateauForm μ A A - ((‖∫ V, A V ∂μ‖ ^ 2 : ℝ) : ℂ)
theorem plateauForm_eq_plateauPairing (μ : Measure (GaugeField a)) (A B : GaugeField a → ℂ) :
    plateauForm μ A B = plateauPairing μ A B :=
  rfl
end YangMills.Construction.InfiniteLattice
