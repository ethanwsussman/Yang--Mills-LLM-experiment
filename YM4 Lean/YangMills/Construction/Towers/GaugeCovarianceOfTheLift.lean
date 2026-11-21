import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LiftGaugeCovariance.Statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (b : CriticalBranchData L n k) (U : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      b.IsCriticalUpTo i → IsFibreCriticalSection (b.gaugeFixedEnergy i) U ε p →
        ForGaugesNearOneOrConstant fun v W =>
          p (PeriodicLattice.gaugeTransform v W) =
              PeriodicLattice.gaugeTransform (blockGaugeLift v) (p W) ∧
            b.gaugeFixedEnergy i (p (PeriodicLattice.gaugeTransform v W)) = b.gaugeFixedEnergy i (p W)
end YangMills.Construction.Tower
end
