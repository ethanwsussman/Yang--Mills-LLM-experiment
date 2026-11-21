import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def inverseExpansionRate (d L : ℕ) : ℝ :=
  min (greenDecayRate d L / 8)
    (Real.exp 1 * lowerBoundConst d * greenDecayRate d L /
      (16 * upperBoundConst d L * latticeSumConst d L (1 / 4 * greenDecayRate d L)))
def expansionDecayRate (d L : ℕ) : ℝ :=
  1 / 2 * min (inverseExpansionRate d L) (1 / 16 * greenDecayRate d L)
def expansionSeparationFloor (d L : ℕ) : ℝ :=
  4 * ((d : ℝ) + 2) * (Real.log (L : ℝ) + 1) / expansionDecayRate d L
def expansionConstFirst (d L : ℕ) (cD : ℝ) : ℝ :=
  4 * cD * upperBoundConst d L / (Real.exp 1 * greenDecayRate d L) +
    12 * (L : ℝ) * (localComparisonConst d L + upperBoundConst d L) / greenDecayRate d L
def expansionConstSecond (d L : ℕ) (cD : ℝ) : ℝ :=
  2 * cD * expansionConstFirst d L cD * latticeSumConst d L (expansionDecayRate d L) /
    lowerBoundConst d
def expansionBlockSizeFloor (d L : ℕ) (cD : ℝ) : ℝ :=
  max (6 * (L : ℝ))
    (2 * expansionConstSecond d L cD * latticeSumConst d L (1 / 2 * expansionDecayRate d L))
def expansionConstBound (d L : ℕ) (cD : ℝ) : ℝ :=
  max ((L : ℝ) ^ 4 * upperBoundConst d L)
    (max (upperBoundConst d L * latticeSumConst d L (1 / 2 * greenDecayRate d L))
      (max (2 / lowerBoundConst d)
        (max ((L : ℝ) ^ 2 * expansionConstSecond d L cD *
            latticeSumConst d L (1 / 2 * expansionDecayRate d L))
          (4 * cD * latticeSumConst d L (1 / 2 * expansionDecayRate d L) / lowerBoundConst d))))
end YangMills.Construction.Weighted
