import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsDefs
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits.TorusTransportOfTuples
def standingParams (D : LimitSetup) (K m : ℕ+) : Conventions.StandingParameters :=
  ⟨D.L, D.standingConstraints.factor_admissible, K, m⟩
end YangMills.Construction.FamiliesOfLimits.TorusTransportOfTuples
end
