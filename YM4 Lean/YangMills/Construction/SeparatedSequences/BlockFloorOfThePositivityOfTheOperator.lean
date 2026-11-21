import YangMills.Construction.SeparatedSequences.NumbersOfTheExpansionOverThePieces
import YangMills.Construction.SeparatedSequences.SquarePartitionFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def slavedPartBound (L : ℕ) : ℝ :=
  max 1 (max (16 * (L : ℝ) ^ 2 * expansionBound L)
    (expansionBound L *
        (12 * (L : ℝ) ^ 4 + 1 + 32 * (L : ℝ) *
          YangMills.Construction.PeriodicLattice.complexBackgroundKernelConstant L) *
      (1 + 32 * (L : ℝ) ^ 2 * expansionBound L)))
def positiveDefiniteBlockSizeFloor (L : ℕ) : ℝ :=
  max (expansionBlockSizeFloor L) (max (squarePartitionConstant L)
    (16 * (pieceOverlapCount L : ℝ) *
      YangMills.Construction.SeparatedSequences.PieceChain.expansionInverseConst L *
      YangMills.Construction.SequenceTriples.commutatorBoundConstant L * squarePartitionConstant L *
      slavedPartBound L))
end YangMills.Construction.SeparatedSequences
end
