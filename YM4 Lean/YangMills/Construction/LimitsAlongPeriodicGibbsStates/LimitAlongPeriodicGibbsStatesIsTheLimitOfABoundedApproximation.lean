import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.FirstPassageSeqs
def originPlaquette (a : ℝ) : InfiniteLattice.ElementaryPlaquette a := ⟨0, 0, 1, by decide⟩
def onSepTuples (σ : EuclideanFunctionals.sepAll → ℝ) (T : SeparatedTuples.SepTuple) : ℝ :=
  σ ⟨T.1, (R4TupleForms.isDisjointlySupported_iff_mem_separatedAll
    EuclideanFunctionals.defaultMirrorData T.1).1 T.2⟩
end YangMills.Construction.FirstPassageSeqs
end
