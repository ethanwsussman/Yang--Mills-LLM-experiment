import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields TorusLumps
def WeightsCloseToBlockMeans : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (t n : ℕ) [NeZero n] (y : TorusSite n),
    (∀ h : PlaquetteWeight (fineSide L t n), |blockMean L t n y h| ≤ weightSup h) ∧
    (∀ (h : PlaquetteWeight (fineSide L t n)) (p : TorusPlaquette (fineSide L t n)), IsPlaquetteAt L t y p →
      |h p - blockMean L t n y h| ≤ 3 * weightLipschitz L t h) ∧
    ∀ (h : PlaquetteWeight (fineSide L (t + 1) n)) (z : TorusSite (n * L)), z ∈ sitesInBlocks L {y} →
      |blockMean L t (n * L) z h - blockMean L (t + 1) n y h| ≤ 3 * weightLipschitz L (t + 1) h
end WeightedResponses
end YangMills.Construction
end
