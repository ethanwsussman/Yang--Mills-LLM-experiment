import YangMills.Construction.SeparatedSequences.PieceOverlapConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def squarePartitionConstant (L : ℕ) : ℝ :=
  8 * (pieceOverlapCount L : ℝ) ^ 5 * piecePartitionConstant L
end YangMills.Construction.SeparatedSequences
end
