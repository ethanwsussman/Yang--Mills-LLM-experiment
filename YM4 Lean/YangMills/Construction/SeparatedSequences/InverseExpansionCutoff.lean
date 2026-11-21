import YangMills.Construction.SeparatedSequences.InverseGreenConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def partitionOfUnityLipschitzConstant (d L : ℕ) : ℝ :=
  6 * (L : ℝ) * (1 + Real.sqrt (6 * 2 ^ d))
def cubeOperatorChangeConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  24 * (d : ℝ) * ((d : ℝ) - 1) * plaquetteColumnConstant d L δ C ^ 2 +
    18 * (d : ℝ) * compressedEntryConstant d L δ C ^ 2
def expansionRemainderConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  3 * 2 ^ d * (2 / compressedGreenLowerBound d 1) * (2 * (d : ℝ)) * expSumConstant d L (δ / 4) *
    (2 * partitionOfUnityLipschitzConstant d L * compressedEntryConstant d L δ C / (Real.exp 1 * δ) +
      cubeOperatorChangeConstant d L δ C * (L : ℝ) ^ (2 * d + 5) * expSumConstant d L (δ / 2) +
      6 * (L : ℝ) * compressedEntryConstant d L δ C / δ)
def inverseExpansionBlockCutoff (d L : ℕ) (δ C m : ℝ) : ℝ :=
  max m (max (12 * (L : ℝ))
    (4 * (d : ℝ) * expSumConstant d L (inverseDecayRate d L δ C / 2) *
      expansionRemainderConstant d L δ C))
end YangMills.Construction.SeparatedSequences
