import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps
def agreeingWeightExtensionStatement : Prop :=
  ∀ (L t : ℕ) [NeZero L] (n n' : ℕ) [NeZero n] [NeZero n'] (y : TorusSite n) (y' : TorusSite n')
    (h : PlaquetteWeight (fineSide L t n)) (h' : PlaquetteWeight (fineSide L t n')),
    Odd L → 8 ≤ n → 8 ≤ n' → WeightsAgreeAt L t y y' h h' →
    ∃ h'' : PlaquetteWeight (fineSide L t n'), (∀ p, IsPlaquetteAt L t y' p → h'' p = h' p) ∧
      weightNorm L t h'' ≤ weightNorm L t h
end YangMills.Construction.WeightedResponses
end
