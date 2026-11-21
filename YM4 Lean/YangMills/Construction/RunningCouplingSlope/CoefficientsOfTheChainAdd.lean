import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open SlopeCoefficient
def ChainSlopeCoefficientsAdd : Prop :=
  ∀ (g : ℝ) (L : ℕ), (∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = g ∧ T.side = L) →
    ∃ b : ℕ → ℝ, AreStepSlopeCoefficients g L b ∧
    ∀ (k : ℕ) (r : ℝ), 0 < r → r ≤ 1 →
      HasSlopeCoefficient Filter.atTop (chainLogarithm g r L k) (∑ l ∈ Finset.range k, b l)
end YangMills.Construction.RunningCouplingSlope
end
