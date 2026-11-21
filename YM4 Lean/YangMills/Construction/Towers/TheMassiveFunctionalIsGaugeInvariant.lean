import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z → ∀ m : ℕ, 0 < m →
    ∀ U ∈ fieldSpace L m 0 0, ∀ v ∈ gaugeGroupAt L m 0 0,
      massiveLogDetFunctional L m z (PeriodicLattice.gaugeTransform v U) =
        massiveLogDetFunctional L m z U
end YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance
end
