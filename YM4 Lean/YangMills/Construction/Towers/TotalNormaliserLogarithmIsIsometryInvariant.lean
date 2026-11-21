import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogTotalNormaliserSymmetryInvariant : Prop :=
  ∀ L n k : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    EventuallyNearIdentity (fieldSpace L n (k + 1) (k + 1)) fun W =>
      ∀ f : YangMills.Construction.PeriodicLattice.FourTorus L n →
          YangMills.Construction.PeriodicLattice.FourTorus L n,
        IsLevelSymmetry (k + 1) (k + 1) f →
        logTotalNormaliserRatio L n (k + 1) (pushField f W) =
          logTotalNormaliserRatio L n (k + 1) W
end YangMills.Construction.Tower
end
