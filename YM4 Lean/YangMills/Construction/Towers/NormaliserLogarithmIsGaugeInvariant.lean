import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogNormaliserRatioGaugeInvariant : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ a : ℕ, a + 1 ≤ k →
    ForGaugesNearOneOrConstant fun v W =>
      logNormaliserRatio L m k a (PeriodicLattice.gaugeTransform v W) = logNormaliserRatio L m k a W
end YangMills.Construction.Tower
end
