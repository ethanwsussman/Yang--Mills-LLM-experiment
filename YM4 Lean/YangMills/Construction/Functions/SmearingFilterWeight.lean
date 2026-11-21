import YangMills.Construction.Functions.TriangleKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter
open scoped ENNReal
open TriangleKernel
def absCoeffSum : ℝ :=
  ∑' j : ℤ, |(smearingSeq j : ℝ)| * (tentFourierCoeff j).re
def filterSeries (u : ℝ) : ℂ :=
  ∑' j : ℤ, (smearingSeq j : ℂ) * tentFourierCoeff j * Complex.exp (Complex.I * j * u)
def weightSeries (t : ℝ) : ℂ :=
  2 * ∑' j : ℕ, (smearingSeq ((j : ℤ) + 1) : ℂ) * tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j
def extendedExpNeg (x : ℝ≥0∞) : ℝ :=
  if x = ∞ then 0 else Real.exp (-x.toReal)
def weightSeriesAtExp (x : ℝ≥0∞) : ℂ :=
  weightSeries (extendedExpNeg x)
def weightConst : ℝ :=
  √2 - 1
end YangMills.Construction.SmearingFilter
