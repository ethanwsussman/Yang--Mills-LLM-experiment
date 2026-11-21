import YangMills.Construction.SeparatedSequences.ExpSiteSeries
import YangMills.Construction.SeparatedSequences.NumbersAndDataOfTheExpansionOfTheInverse
import YangMills.Construction.SeparatedSequences.PieceOverlapConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.PieceChain
def sourceDatumConst (L : ℕ) : ℝ :=
  128 * expansionInverseConst L * (YangMills.Construction.SeparatedSequences.pieceOverlapCount L : ℝ) *
    YangMills.Construction.SeparatedSequences.expSiteSeries L
      (1 / 2 * YangMills.Construction.SeparatedSequences.blockOperatorRate L)
end YangMills.Construction.SeparatedSequences.PieceChain
end
