import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LiftSymmetryCovariance.Statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (b : CriticalBranchData L n k) (U : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      b.IsCriticalUpTo i → IsFibreCriticalSection (b.gaugeFixedEnergy i) U ε p →
        EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
          ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
            IsLevelSymmetry k (i + 1) f →
            p (pushField f W) = pushField f (p W) ∧
              b.gaugeFixedEnergy i (p (pushField f W)) = b.gaugeFixedEnergy i (p W)
end YangMills.Construction.Tower
end
