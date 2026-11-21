import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WilsonLaw
def LiftedWilsonMeasureIsProbability : Prop :=
  ∀ (L e K : ℕ) (β : ℝ), 1 < L → IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure L e K β)
end WilsonLaw
end YangMills.Construction
end
