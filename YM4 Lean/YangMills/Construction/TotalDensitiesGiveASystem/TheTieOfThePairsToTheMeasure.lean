import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
def PairsTiedToWilsonMeasure : Prop :=
  HoldsAtAdmissibleParameters fun T y => ∃ CT : ℝ, 0 < CT ∧
    ForSmallCoupling fun g => TotalDensitySystem.CouplingTie (T.stepParameters y) (2 * T.B) CT g
end YangMills.Construction.TotalDensities
end
