import YangMills.Construction.Lattice.CommutatorsOfTheSystemWithAFunction
import YangMills.Construction.SeparatedSequences.NumbersAndDataOfTheExpansionOfTheInverse
import YangMills.Construction.SeparatedSequences.PieceOverlapConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences
def expansionRatioConst (L : ℕ) : ℝ :=
  2 * Real.exp (2 * YangMills.Construction.Lattice.siteNearnessRadius L + 8) *
    YangMills.Construction.SequenceTriples.commutatorBoundConstant L *
    piecePartitionConstant L * PieceChain.expansionInverseConst L
def expansionBlockSizeFloor (L : ℕ) : ℝ :=
  max (2 * (pieceOverlapCount L : ℝ) * expansionRatioConst L)
    ((4 * (L : ℝ) ^ 3 + 2) * piecePartitionConstant L)
def cutoffSeparation (L : ℕ) (M : ℝ) : ℝ := M / (8 * (L : ℝ))
def expansionBound (L : ℕ) : ℝ :=
  16 * (pieceOverlapCount L : ℝ) * PieceChain.expansionInverseConst L
end YangMills.Construction.SeparatedSequences
end
