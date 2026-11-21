import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
def FlowPasses : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => ∃ (c : ℝ) (Nw : ℕ), 0 ≤ c ∧ 1 ≤ Nw ∧
    ∀ c₅ : ℝ, c ≤ c₅ → TotalDensities.ForSmallCoupling fun g =>
    TotalDensitySystem.FlowPassage (T.stepParameters y) (2 * T.B) c₅
      (3 / 4 * TotalDensitySystem.oneLoopShift T.side) Nw g
end YangMills.Construction.TotalDensities
end
