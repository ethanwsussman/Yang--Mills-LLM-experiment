import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def GaugeTransformPropertiesForAllSpacings : Prop :=
  ∀ a : ℝ, 0 < a → GaugeTransformProperties a
end YangMills.Construction.InfiniteLattice
