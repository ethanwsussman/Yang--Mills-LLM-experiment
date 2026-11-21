import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps RenormalizationStepParameters WeightedResponses TorusFields
def longSupportPriceSumStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (x : ℕ → ℝ) (k : ℕ), (∀ j ≤ k, y ≤ x j) →
    (∀ j < k, |x (j + 1) - x j| ≤ 2 * Tb.B) →
    ∑ j ∈ Finset.range k, Real.exp (-(800 * Tb.gasRate * x j * ((k : ℝ) - j))) ≤
      Real.exp (-(x k * Tb.κ₁ * Tb.threshold ^ 2))
end YangMills.Construction.CellWindows
end
