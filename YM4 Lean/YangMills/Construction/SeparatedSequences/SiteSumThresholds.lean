import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def siteSumThreshold (d L : ℕ) (a : ℝ) : ℝ :=
  2 * ((d : ℝ) * Real.log (L : ℝ) + 1) / a
def siteSumMajorant (d L : ℕ) (a : ℝ) : ℝ :=
  8 * (L : ℝ) ^ d * (2 + 4 / a) ^ d
end YangMills.Construction.SeparatedSequences
end
