import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
def componentCumulantOne (s : SepTuple → ℝ) (X : SeparatedTuples.SepTuple) (l : Fin X.1.length) : ℝ :=
  cumulantOne s (X.1.get l) ((TupleLists.get_mem_disjointSupportTuples X).1 l)
def centringCoeff (s : SepTuple → ℝ) (X : SeparatedTuples.SepTuple) (A : Finset ℕ) : ℂ :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin X.1.length => (l : ℕ) + 1 ∉ A),
    ((-componentCumulantOne s X l : ℝ) : ℂ)
def centredTuple (s : SepTuple → ℝ) (X : SeparatedTuples.SepTuple) : SeparatedTuples.FormalSpan :=
  ∑ A ∈ (Finset.Icc 1 X.size).powerset,
    centringCoeff s X A • SeparatedTuples.basisVec (X.subtuple A)
def centring (s : SepTuple → ℝ) :
    SeparatedTuples.FormalSpan →ₗ[ℂ] SeparatedTuples.FormalSpan :=
  SeparatedTuples.linearExtend (centredTuple s)
theorem centring_basisVec (s : SepTuple → ℝ) (X : SeparatedTuples.SepTuple) :
    centring s (SeparatedTuples.basisVec X) = centredTuple s X :=
  SeparatedTuples.linearExtend_basisVec _ X
end YangMills.Construction.TestSpaces
end
