import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
def cellRadius (d L : ℕ) : ℝ := ((d : ℝ) + 1) * (L : ℝ)
def expSumConstant (d L : ℕ) (α : ℝ) : ℝ :=
  9 * (L : ℝ) ^ d * (2 * (1 + 2 / α)) ^ d
def testFormEnergyConstant (d : ℕ) : ℝ :=
  4 / 3 * (d : ℝ) * 63 ^ 2 * (9 / 4 : ℝ) ^ (d - 1)
def compressedGreenLowerBound (d : ℕ) (a : ℝ) : ℝ :=
  (12 * testFormEnergyConstant d + a)⁻¹
end SeparatedSequences
end YangMills.Construction
end
