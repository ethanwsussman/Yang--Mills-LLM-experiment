import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
def CouplingConstantsExist : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => ∃ c : ℝ, ∀ c₅ : ℝ, c ≤ c₅ →
    TotalDensities.ForSmallCoupling fun g =>
    TotalDensitySystem.CouplingConstants (T.stepParameters y) (2 * T.B) c₅
      (3 / 4 * TotalDensitySystem.oneLoopShift T.side) g
end YangMills.Construction.TotalDensities
end
