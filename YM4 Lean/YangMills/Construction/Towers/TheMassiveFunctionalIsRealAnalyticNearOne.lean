import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveLogDet
def AnalyticNearIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    PeriodicOperators.Tempered.EventuallyForSides L fun n =>
      PeriodicOperators.Tempered.IsAnalyticNearIdentity (massiveLogDetFunctional L n z)
end YangMills.Construction.Tower.MassiveLogDet
end
