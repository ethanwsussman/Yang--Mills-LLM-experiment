import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields StepSettings WeightedResponses BlockAverages
namespace AgreeingWeights
def WeightsAgreeingOnBlock : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L →
    (∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (Y : TorusSite n) (Y' : TorusSite n')
      (h : PlaquetteWeight (fineSide L (t + 1) n)) (h' : PlaquetteWeight (fineSide L (t + 1) n')),
      WeightsAgreeAt L (t + 1) Y Y' h h' → ∀ o ∈ centredCube L,
      WeightsAgreeAt L t (fineSite L Y 0 o) (fineSite L Y' 0 o) h h') ∧
    (∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (y : TorusSite n) (y' : TorusSite n')
      (h : PlaquetteWeight (fineSide L t n)) (h' : PlaquetteWeight (fineSide L t n')),
      WeightsAgreeAt L t y y' h h' → blockMean L t n y h = blockMean L t n' y' h') ∧
    ∀ (r s n n' : ℕ) [NeZero n] [NeZero n'], 3 ≤ n → 3 ≤ n' → ∀ (Y : TorusSite n) (Y' : TorusSite n')
      (h : PlaquetteWeight (fineSide L r n)) (h' : PlaquetteWeight (fineSide L r n')),
      WeightsAgreeAt L r Y Y' h h' →
      ∃ g : PlaquetteWeight (fineSide L r n'), (∀ p, IsPlaquetteAt L r Y' p → g p = h' p) ∧
        weightNorm L s g ≤ weightNorm L s h ∧ WeightsAgreeAt L r Y Y' h g
end AgreeingWeights
end YangMills.Construction
end
