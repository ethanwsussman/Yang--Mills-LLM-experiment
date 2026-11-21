import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfTheMainStatement
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def VolumeFirstLimitExtras : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => TotalDensities.ForSmallCoupling fun g =>
    ∀ (Q : SystemsWithFiveBounds.PairSequence (T.stepParameters y).side
        (TotalDensitySystem.IsFirstPassagePair (T.stepParameters y) (2 * T.B) g))
      (S : LimitTheorem.CumulantFamily),
      Q.Defines S → TotalDensitySystem.VolumeFirstExtras (T.stepParameters y) Q S ∧
        TotalDensities.ShortDistanceAsymptotics S
end YangMills.Construction.TotalDensities
end
