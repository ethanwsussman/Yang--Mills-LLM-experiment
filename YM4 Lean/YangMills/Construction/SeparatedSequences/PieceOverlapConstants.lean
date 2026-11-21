import YangMills.Construction.SeparatedSequences.PieceCutoff
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def pieceOverlapCount (L : ℕ) : ℕ :=
  ((4 * L ^ 2 + 3) * L ^ 2) ^ 4
def pieceCutoffDerivBound : ℝ :=
  max 1 (max (⨆ x, |deriv pieceCutoff x|)
    (max (⨆ x, |deriv pieceCutoff x| ^ 2)
      (⨆ x, |deriv (deriv pieceCutoff) x|)))
def piecePartitionConstant (L : ℕ) : ℝ :=
  2304 * (1 + (pieceOverlapCount L : ℝ)) * (1 + 2 * (pieceOverlapCount L : ℝ)) * (L : ℝ) ^ 4 *
    pieceCutoffDerivBound
end YangMills.Construction.SeparatedSequences
