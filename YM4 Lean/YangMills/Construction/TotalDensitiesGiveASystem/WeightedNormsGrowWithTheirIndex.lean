import YangMills.Construction.Continuum.NormsOfASchwartzFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open ConfigSpace
def BracketNormMonotone : Prop :=
  ∀ (n k k' : ℕ) (f : SchwartzFn n), k ≤ k' → bracketNorm k f ≤ bracketNorm k' f
end YangMills.Construction.TotalDensitiesGiveASystem
end
