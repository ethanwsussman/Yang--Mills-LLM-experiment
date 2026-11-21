import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages RenormalizationStepParameters TorusLumps
namespace RunningCouplingSlope
def MinimalActionMomentNearOne : Prop :=
  ∃ C c : ChainParameters → ℝ, (∀ l, 0 < C l) ∧ (∀ l, 0 < c l) ∧ ∀ T : ParameterAssignment, T.Admissible →
    ∀ (t n : ℕ) [NeZero n] (X : imaginaryQuaternions), 64 ≤ n → ‖X‖ = 1 →
      |gaugeTotalMoment (minimalActionTotal T.coupling T.side (t + 1)) n X - 1| ≤
        C T.toChainParameters * Real.exp (-(c T.toChainParameters * n))
end RunningCouplingSlope
end YangMills.Construction
end
