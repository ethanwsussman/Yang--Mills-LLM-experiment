import YangMills.Construction.SeparatedSequences.NumbersOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.CombinedConstants
def derivedRate (L : ℕ) : ℝ :=
  min (1 / 4 * dirichletDecay L) (min (1 / 2 * expansionDecay L) (1 / 2 * propagatorDecay L))
def derivedGapLower (L : ℕ) : ℝ :=
  max (gapLower L)
    (max (siteSumThreshold 4 L (1 / 4 * derivedRate L))
      (max (4 * (4 + 2) * Real.log (L : ℝ) / derivedRate L) (2 * (L : ℝ))))
end YangMills.Construction.SeparatedSequences.CombinedConstants
end
