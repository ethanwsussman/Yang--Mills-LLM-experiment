import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
structure NormaliserProductProperties (L m k : ℕ) (hL : 0 < L) : Prop where
  wellDefined : EventuallyNearIdentity (fieldSpace L m (k + 1) (k + 1)) fun W =>
    TotalNormaliserWellDefined W
  prod_eq : EventuallyNearIdentity (fieldSpace L m (k + 1) (k + 1)) fun W =>
    totalGaussianNormaliser L m (k + 1) W =
      ∏ i : Fin (k + 1), gaussianNormaliser L m (k + 1) i (descendingChain W i.is_lt)
  log_eq : EventuallyNearIdentity (fieldSpace L m (k + 1) (k + 1)) fun W =>
    LogTotalNormaliserWellDefined W ∧
      LogLevelNormaliserWellDefined hL (Nat.le_succ k) (chosenProlong L m (k + 1) k W) ∧
      logTotalNormaliserRatio L m (k + 1) W =
        logNormaliserRatio L m (k + 1) k W +
          logLevelNormaliserRatio hL (Nat.le_succ k) (chosenProlong L m (k + 1) k W)
  analytic : ∃ N : Set (Edge L m (k + 1) (k + 1) → Matrices.ComplexMatrix2),
    IsOpenNhdOfOne N ∧ IsAnalyticFieldFunction N (logTotalNormaliserRatio L m (k + 1))
  gauge_invariant : ForGaugesNearOneOrConstant fun g W =>
    logTotalNormaliserRatio L m (k + 1) (PeriodicLattice.gaugeTransform g W) =
      logTotalNormaliserRatio L m (k + 1) W
  symmetry_invariant : EventuallyNearIdentity (fieldSpace L m (k + 1) (k + 1)) fun W =>
    ∀ σ : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
      IsLevelSymmetry (k + 1) (k + 1) σ →
      logTotalNormaliserRatio L m (k + 1) (pushField σ W) =
        logTotalNormaliserRatio L m (k + 1) W
def NormaliserProductTheorem : Prop :=
  ∀ L m k : ℕ, ∀ hL : Conventions.IsAdmissibleBlockingFactor L, 0 < m →
    NormaliserProductProperties L m k (lt_of_lt_of_le (by norm_num) hL.2)
end YangMills.Construction.Tower
end
