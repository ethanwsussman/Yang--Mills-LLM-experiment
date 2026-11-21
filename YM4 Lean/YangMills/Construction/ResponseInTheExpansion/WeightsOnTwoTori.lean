import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields StepSettings BlockAverages
def WeightsCompatibleAcrossTori : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (t n n' : ℕ) [NeZero n] [NeZero n'],
    (∀ (y : TorusSite n) (y' : TorusSite n') (h : PlaquetteWeight (fineSide L (t + 1) n))
      (h' : PlaquetteWeight (fineSide L (t + 1) n')),
      WeightsAgreeAt L (t + 1) y y' h h' → ∀ o ∈ centredCube L,
        WeightsAgreeAt L t (fineSite L y 0 o) (fineSite L y' 0 o) h h') ∧
    (∀ (y : TorusSite n) (y' : TorusSite n') (h : PlaquetteWeight (fineSide L t n))
      (h' : PlaquetteWeight (fineSide L t n')),
      WeightsAgreeAt L t y y' h h' → blockMean L t n y h = blockMean L t n' y' h') ∧
    ∀ h : PlaquetteWeight (fineSide L t n), weightNorm L t h ≤ weightNorm L (t + 1) h
end YangMills.Construction.WeightedResponses
end
