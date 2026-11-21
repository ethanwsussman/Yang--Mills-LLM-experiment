import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def LocalFunctionPropertiesForAllSpacings : Prop :=
  ∀ a : ℝ, 0 < a → LocalFunctionProperties a
end YangMills.Construction.InfiniteLattice
