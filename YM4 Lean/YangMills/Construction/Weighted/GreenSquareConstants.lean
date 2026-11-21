import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Weighted
def greenDecayRate (d L : ℕ) : ℝ := 1 / (20 * (d : ℝ) * (L : ℝ))
def coercivityConst (L : ℕ) : ℝ := 1 - ((L : ℝ) ^ 2)⁻¹
def weightedBoundConst (d L : ℕ) : ℝ :=
  Real.exp (greenDecayRate d L * ((d : ℝ) + 1)) *
    (4 / coercivityConst L + Real.sqrt (8 / coercivityConst L) +
      8 * greenDecayRate d L * (L : ℝ) * Real.sqrt (d : ℝ) / coercivityConst L)
def latticeSumConst (d L : ℕ) (κ : ℝ) : ℝ :=
  8 * (L : ℝ) ^ d * (2 + 4 / κ) ^ d
def latticeSumRadius (d L : ℕ) (κ : ℝ) : ℝ :=
  2 * ((d : ℝ) * Real.log (L : ℝ) + 1) / κ
def upperBoundConst (d L : ℕ) : ℝ :=
  weightedBoundConst d L ^ 2 * (L : ℝ) ^ 2 * latticeSumConst d L (1 / 4 * greenDecayRate d L)
def testLaplacianConst (d : ℕ) : ℝ := (d : ℝ) * 2 ^ (d + 1) * Real.pi ^ 2
def lowerBoundBaseConst (d : ℕ) : ℝ := (2 * (d : ℝ) + 1) * testLaplacianConst d + 1
def lowerBoundConst (d : ℕ) : ℝ := (lowerBoundBaseConst d ^ 2)⁻¹
def domainComparisonConst (d L : ℕ) : ℝ :=
  3 * (L : ℝ) * (Real.sqrt (d : ℝ) + 2) * weightedBoundConst d L ^ 2
def localComparisonConst (d L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 *
      (weightedBoundConst d L +
        domainComparisonConst d L * latticeSumConst d L (1 / 4 * greenDecayRate d L)) ^ 2 *
    latticeSumConst d L (1 / 16 * greenDecayRate d L)
end Weighted
end YangMills.Construction
