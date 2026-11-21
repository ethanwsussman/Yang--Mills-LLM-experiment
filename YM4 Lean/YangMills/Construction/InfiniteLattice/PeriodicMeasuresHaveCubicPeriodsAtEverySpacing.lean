import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodicMeasuresCubicInvarianceAllSpacings : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β → PeriodicMeasuresCubicInvariance ha β
end YangMills.Construction.InfiniteLattice
end
