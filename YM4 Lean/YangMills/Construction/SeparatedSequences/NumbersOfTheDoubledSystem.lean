import YangMills.Construction.Lattice.FourLocalMapsOfTheDoubledSystem
import YangMills.Construction.Lattice.NumberOfTheCommutatorsInTheWeightedNorms
import YangMills.Construction.SeparatedSequences.NumbersOfTheEnds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.DoubledSystemConstants
def midExponent (β : ℝ) : ℝ := 1 / 2 * (1 + β)
def maxEndBound (L : ℕ) (β : ℝ) : ℝ :=
  max (EndConstants.mainBound L β β)
    (max (EndConstants.mainBound L β (1 / 2 * (1 - β)))
      (EndConstants.mainBound L (midExponent β) (midExponent β)))
def localConst (L : ℕ) (β : ℝ) : ℝ :=
  6 * maxEndBound L β *
    (2 + SequenceTriples.doubledLocalMapsConst L * Real.exp (Lattice.siteNearnessRadius L) *
      (1 + maxEndBound L β))
def inverseConst (L : ℕ) : ℝ :=
  Real.exp 8 * max (PieceChain.expansionInverseConst L) (localConst L (1 / 2))
def ratioConst (L : ℕ) : ℝ :=
  (3 + 12 * (L : ℝ) ^ 3) * Real.exp (Lattice.siteNearnessRadius L + 2) *
      (SequenceTriples.commutatorBoundConstant L +
        WeightedCommutatorConstants.weightedCommutatorConstant L +
        SequenceTriples.doubledLocalMapsConst L) *
    piecePartitionConstant L * inverseConst L
def blockLower (L : ℕ) : ℝ :=
  max (EndConstants.blockLower L) (2 * (pieceOverlapCount L : ℝ) * ratioConst L)
end YangMills.Construction.SeparatedSequences.DoubledSystemConstants
end
