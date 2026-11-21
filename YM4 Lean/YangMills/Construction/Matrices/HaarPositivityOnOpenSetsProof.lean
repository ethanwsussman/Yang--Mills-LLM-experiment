import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.Matrices.HaarPositivityOnOpenSets
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
theorem openPositiveStatement_holds (hG : FiniteProductGroupStatement) :
    HaarPositivity.OpenPositiveStatement := by
  intro S _ O hO hne
  obtain ⟨hTop, hCompact, -⟩ := hG.1 S
  obtain ⟨hBorel, -, hProb, hLeft, -⟩ := hG.2.1 S
  have : BorelSpace (S → specialUnitary) := ⟨hBorel.symm⟩
  have : (haarPi S).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by simp)
  exact hO.measure_pos (haarPi S) hne
end YangMills.Construction.Matrices.ComplexMatrix2
