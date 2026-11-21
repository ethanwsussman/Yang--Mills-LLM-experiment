import YangMills.Construction.SeparatedSequences.ExplicitConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
def greenColumnConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  (1 + (L : ℝ) ^ d) * C * Real.exp (δ * cellRadius d L)
def compressedEntryConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  greenColumnConstant d L δ C * Real.exp (δ * cellRadius d L)
def plaquetteColumnConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  4 * (L : ℝ) ^ 2 * greenColumnConstant d L δ C * Real.exp (δ * (d : ℝ))
def inverseDecayRate (d L : ℕ) (δ C : ℝ) : ℝ :=
  min (δ / 4)
    (compressedGreenLowerBound d 1 * δ /
      (8 * (d : ℝ) * compressedEntryConstant d L δ C * expSumConstant d L (δ / 2)))
def halfInverseDecayRate (d L : ℕ) (δ C : ℝ) : ℝ :=
  1 / 2 * inverseDecayRate d L δ C
def inverseKernelConstant (d L : ℕ) : ℝ :=
  2 * (compressedGreenLowerBound d 1)⁻¹ * (L : ℝ) ^ ((d : ℝ) / 2 - 1)
def fieldKernelConstant (d L : ℕ) (δ C : ℝ) : ℝ :=
  2 * (d : ℝ) * (L : ℝ) ^ 2 * greenColumnConstant d L δ C * inverseKernelConstant d L *
    expSumConstant d L (δ / 4)
def gapBlockThreshold (d L : ℕ) (δ C r₀ : ℝ) : ℝ :=
  max r₀ (8 / inverseDecayRate d L δ C * ((d : ℝ) * Real.log (L : ℝ) + Real.log 2))
end SeparatedSequences
end YangMills.Construction
