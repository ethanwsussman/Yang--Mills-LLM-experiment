import YangMills.Construction.SeparatedSequences.CeilingOfTheDataAtTheEnds
import YangMills.Construction.SeparatedSequences.SourceDatumNumberOfTheExpansion
import Mathlib
noncomputable section
namespace YangMills.Construction.SeparatedSequences.PieceChain
def treePairRadius (L : ℕ) : ℝ :=
  EndConstants.endDataCeiling L / (2 * sourceDatumConst L)
end YangMills.Construction.SeparatedSequences.PieceChain
end
