import YangMills.Construction.SeparatedSequences.NumbersOfTheEnds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.EndConstants
def endRatio (L : ℕ) (M : ℝ) : ℝ :=
  SeparatedSequences.EndConstants.ratioConst L * M⁻¹ *
    Real.exp (-(SeparatedSequences.blockOperatorRate L * SeparatedSequences.cutoffSeparation L M))
end YangMills.Construction.SeparatedSequences.EndConstants
end
