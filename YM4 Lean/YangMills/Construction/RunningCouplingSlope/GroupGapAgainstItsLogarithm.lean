import YangMills.Construction.RunningCouplingSlope.FamiliesOfExponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open LaplaceAsymptotics
def HaarGapSubLogDerivBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
    |s * deriv haarGapSubLog s| ≤ C / s ∧ |s ^ 2 * iteratedDeriv 2 haarGapSubLog s| ≤ C / s
end YangMills.Construction.RunningCouplingSlope
end
