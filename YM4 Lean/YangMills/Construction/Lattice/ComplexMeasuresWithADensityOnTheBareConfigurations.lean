import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def bareProductHaar (L m K : ℕ) : Measure (gaugeFieldsAtLevel L m K 0) :=
  (productHaarMeasure L m (levelDepth K 0)).comap Subtype.val
def densityMeasure (f : gaugeFieldsAtLevel L m K 0 → ℂ) :
    ComplexMeasure (gaugeFieldsAtLevel L m K 0) :=
  (bareProductHaar L m K).withDensityᵥ f
def boltzmannMeasure (L m K : ℕ) (β : ℝ) : ComplexMeasure (gaugeFieldsAtLevel L m K 0) :=
  densityMeasure fun U => (boltzmannWeight β U.1 : ℂ)
end YangMills.Construction.PeriodicLattice
end
