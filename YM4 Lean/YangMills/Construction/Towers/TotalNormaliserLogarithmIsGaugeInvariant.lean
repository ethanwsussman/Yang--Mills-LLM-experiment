import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogTotalNormaliserGaugeInvariant : Prop :=
  ∀ L n k : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ForGaugesNearOneOrConstant (L := L) (n := n) (k := k + 1) (j := k + 1) fun v W =>
      logTotalNormaliserRatio L n (k + 1) (YangMills.Construction.PeriodicLattice.gaugeTransform v W) =
        logTotalNormaliserRatio L n (k + 1) W
end YangMills.Construction.Tower
end
