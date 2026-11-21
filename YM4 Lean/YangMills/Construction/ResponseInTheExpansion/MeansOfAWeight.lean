import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields
def BlockMeanIsLinearAndLocal : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (t n : ℕ) [NeZero n] (y : TorusSite n),
    blockMean L t n y (constOneWeight _) = 1 ∧
    (∀ (r r' : ℝ) (h h' : PlaquetteWeight (fineSide L t n)),
      blockMean L t n y (fun p => r * h p + r' * h' p) = r * blockMean L t n y h + r' * blockMean L t n y h') ∧
    ∀ h h' : PlaquetteWeight (fineSide L t n), (∀ p, IsPlaquetteAt L t y p → h p = h' p) →
      blockMean L t n y h = blockMean L t n y h'
end WeightedResponses
end YangMills.Construction
end
