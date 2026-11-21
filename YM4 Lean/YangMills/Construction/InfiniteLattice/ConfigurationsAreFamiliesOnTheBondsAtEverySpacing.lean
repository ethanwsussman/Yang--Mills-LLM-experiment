import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def GaugeFieldsAreLinkFamiliesForAllSpacings : Prop :=
  ∀ (a : ℝ) (ha : 0 < a), GaugeFieldsAreLinkFamilies ha
end YangMills.Construction.InfiniteLattice
