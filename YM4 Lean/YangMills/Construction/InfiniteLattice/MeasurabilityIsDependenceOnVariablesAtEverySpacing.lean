import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def MeasurableIffDependsOnlyAllSpacings : Prop :=
  ∀ a : ℝ, 0 < a → MeasurableIffDependsOnly a
end YangMills.Construction.InfiniteLattice
end
