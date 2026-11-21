import YangMills.Construction.Towers.TheMassiveFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveLogDet
def IsometryInvariance : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z → ∀ n : ℕ, 0 < n →
    ∀ U ∈ fieldSpace L n 0 0,
      ∀ σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving σ →
        MapsSublatticeOnto 0 0 σ →
          massiveLogDetFunctional L n z (pushField (k := 0) (j := 0) σ U) =
            massiveLogDetFunctional L n z U
end YangMills.Construction.Tower.MassiveLogDet
end
