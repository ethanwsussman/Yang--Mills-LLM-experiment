import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def FiniteHaarIntegralsBoundedAtAllSpacings : Prop :=
  ∀ a : ℝ, 0 < a → FiniteHaarIntegralsBounded a
end YangMills.Construction.InfiniteLattice
end
