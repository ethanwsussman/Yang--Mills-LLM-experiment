import YangMills.Construction.Lattice.LeastNumberOfTheBoundOfTheCommutatorOfTheCoupling
import YangMills.Construction.SeparatedSequences.LocalSettingOfAPiece
import YangMills.Construction.SeparatedSequences.NumbersOfTheDoubledSystem
import YangMills.Construction.SeparatedSequences.TreeExpansionDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.ThreeSystemConstants
def pairedAltRatioConst (L : ℕ) : ℝ :=
  2 * Real.exp (2 * Lattice.siteNearnessRadius L + 4) *
      (SequenceTriples.commutatorBoundConstant L + SequenceTriples.sourceCommutatorLeastConstant L) *
    SeparatedSequences.piecePartitionConstant L * SeparatedSequences.DoubledSystemConstants.localConst L (1 / 2)
def localInverseConst (L : ℕ) : SeparatedSequences.PieceChain.LocalBlockIndex → ℝ
  | .single _ => SeparatedSequences.PieceChain.expansionInverseConst L
  | .paired =>
    max (SeparatedSequences.DoubledSystemConstants.inverseConst L)
      (Real.exp 4 * SeparatedSequences.DoubledSystemConstants.localConst L (1 / 2))
def localRatio (L : ℕ) (M : ℝ) : SeparatedSequences.PieceChain.LocalBlockIndex → ℝ
  | .single _ => SeparatedSequences.EndConstants.endRatio L M
  | .paired =>
    max (SeparatedSequences.DoubledSystemConstants.ratioConst L) (pairedAltRatioConst L) * M⁻¹ *
      Real.exp (-(SeparatedSequences.blockOperatorRate L * M / (8 * (L : ℝ))))
def localExpansionConst (L : ℕ) (i : SeparatedSequences.PieceChain.LocalBlockIndex) : ℝ :=
  16 * (SeparatedSequences.pieceOverlapCount L : ℝ) * localInverseConst L i
def pairedTermConst (L : ℕ) : ℝ :=
  8 * localInverseConst L .paired * SeparatedSequences.treeOperatorConst L *
    Real.exp (Lattice.siteNearnessRadius L) * SeparatedSequences.PieceChain.sourceDatumConst L
def pairedWalkConst (L : ℕ) : ℝ :=
  162 * (SeparatedSequences.pieceOverlapCount L : ℝ) * Real.exp (Lattice.siteNearnessRadius L) *
    max 1 (pairedTermConst L)
structure IsPairedBlockScale (L : ℕ) (M : ℝ) : Prop where
  ratio_le : localRatio L M .paired ≤ M ^ (-9 : ℤ)
  operator_mul_le_one :
    4 * SeparatedSequences.treeOperatorConst L * localExpansionConst L .paired *
        SeparatedSequences.PieceChain.sourceDatumConst L * (SeparatedSequences.pieceOverlapCount L : ℝ) *
        Real.exp (Lattice.siteNearnessRadius L) * SeparatedSequences.treeRatio L M ≤ 1
  treeWalk_mul_le :
    2 * (SeparatedSequences.treeExpansionTreeWalkCount L : ℝ) * pairedWalkConst L ≤ M ^ 3
  walkConst_le : pairedWalkConst L ≤ SeparatedSequences.treeWalkConst L * M ^ 2
def pairedBlockLower (L : ℕ) : ℝ :=
  sInf {N : ℝ | max (SeparatedSequences.treeBlockLower L)
      (SeparatedSequences.DoubledSystemConstants.blockLower L) ≤ N ∧
    ∀ M : ℝ, N ≤ M → IsPairedBlockScale L M}
end YangMills.Construction.SeparatedSequences.ThreeSystemConstants
end
