import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def IsLatticeState (ρ : Measure (GaugeField a)) : Prop := IsProbabilityMeasure ρ
def stateEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Measure (GaugeField a)) (Ψ : GaugeField a → E) : E :=
  ∫ U, Ψ U ∂ρ
end InfiniteLattice
end YangMills.Construction
