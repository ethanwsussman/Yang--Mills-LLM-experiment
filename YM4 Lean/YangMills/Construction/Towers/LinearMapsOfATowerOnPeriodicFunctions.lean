import YangMills.Construction.Towers.FunctionsOfTwoSidesAndTheirMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.PeriodicTowerMaps
open OneStepChart
def AgreeWithTorusMaps : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k, 0 < m → PeriodicCompatibility L m k
end YangMills.Construction.Tower.UnitScale.PeriodicTowerMaps
end
