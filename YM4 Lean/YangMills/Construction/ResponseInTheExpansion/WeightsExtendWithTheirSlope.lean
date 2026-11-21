import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps
def weightExtensionLipschitzStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (t n n' : ℕ) [NeZero n] [NeZero n'], 4 ≤ n → 4 ≤ n' →
    ∀ (y : TorusSite n) (y' : TorusSite n') (h : PlaquetteWeight (fineSide L t n)),
      ∃ h' : PlaquetteWeight (fineSide L t n'), WeightsAgreeAt L t y y' h h' ∧ weightSup h' ≤ weightSup h ∧
        weightLipschitz L t h' ≤ weightLipschitz L t h
end YangMills.Construction.WeightedResponses
end
