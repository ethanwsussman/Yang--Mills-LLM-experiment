import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseIntegral
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields StepSettings WeightedResponses
def blockResponseIntegralIsometryInvariantStatement : Prop :=
  ∀ (R : StepSetup) (A : ResponseSetup R), R.IsWellPosed → A.IsAdmissible → ∀ (n : ℕ) [NeZero n],
    R.params.n₀ ≤ n →
    ∀ (g : TorusIsometry) (y : TorusSite n) (V V' : TorusField n), g.Transports V V' →
      blockResponseIntegral A V' (g.mapSite y) = blockResponseIntegral A V y
end YangMills.Construction.ResponseInTheExpansion
end
