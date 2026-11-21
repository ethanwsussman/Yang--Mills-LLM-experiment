import YangMills.Construction.TotalDensitiesGiveASystem.ReconstructionOfAFamilyWithABound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
def BallBoundPassesToLimit : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (Q : ToriSequence L) (c : ℕ → ℝ → ℝ → ℝ),
    (∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ c n d R) → Q.HasBallwiseBound c →
    ∀ S : LimitTheorem.CumulantFamily, Q.HasCumulantLimit S → HasBallSupportBound c S
end YangMills.Construction.TotalDensities
end
