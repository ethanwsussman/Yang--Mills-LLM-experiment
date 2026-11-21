import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.TopStatementDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
def SubsequenceLimitsExist : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => TotalDensities.ForSmallCoupling fun g =>
    TotalDensitySystem.HasTorusSubsequenceLimits (T.stepParameters y) (2 * T.B) g ∧
    TotalDensitySystem.HasGrowingTorusSubsequenceLimits (T.stepParameters y) (2 * T.B) g ∧
    TotalDensitySystem.HasVolumeFirstLimits (T.stepParameters y) (2 * T.B) g
end YangMills.Construction.TotalDensities
end
