import YangMills.Construction.SeparatedSequences.NumbersOfTheEnds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.EndConstants
def endDataCeiling (L : ℕ) : ℝ :=
  min (SeparatedSequences.PieceChain.expansionSmallness L)
    (SeparatedSequences.EndConstants.endsSmallness L /
      (4 * SeparatedSequences.restrictedTripleConst L))
end YangMills.Construction.SeparatedSequences.EndConstants
end
