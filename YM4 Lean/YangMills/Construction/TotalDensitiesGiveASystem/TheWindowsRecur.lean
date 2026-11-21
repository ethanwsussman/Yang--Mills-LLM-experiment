import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open TotalDensities
def FirstPassageWindowsRecur : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∃ N : ℕ, 1 ≤ N ∧ ForSmallCoupling fun g => ∀ K' : ℕ, ∃ K : ℕ,
    K' < K ∧ K ≤ K' + N ∧ ∃ β, IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β
end YangMills.Construction.TotalDensitiesGiveASystem
end
