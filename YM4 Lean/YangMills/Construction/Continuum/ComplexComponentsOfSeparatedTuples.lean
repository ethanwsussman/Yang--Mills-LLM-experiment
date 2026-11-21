import YangMills.Construction.Continuum.ComplexTestFunctionsOfFourSpace
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ComplexTupleComponents
open ComplexTestFunctions
open InfiniteLattice (GaugeField)
open SeparatedTuples (RealValued SepTuple FormalSpan basisVec IsDisjointlySupported)
open R4TupleForms (FinTuple)
open AmbientPoints
theorem tsupport_rePart_subset (f : ComplexValued) :
    tsupport (ComplexTestFunctions.rePart f) ⊆ tsupport f :=
  closure_mono fun x hx h => hx (by simp [ComplexTestFunctions.rePart, h])
theorem tsupport_imPart_subset (f : ComplexValued) :
    tsupport (ComplexTestFunctions.imPart f) ⊆ tsupport f :=
  closure_mono fun x hx h => hx (by simp [ComplexTestFunctions.imPart, h])
theorem rePart_isC1c {f : ComplexValued} (hf : IsC1cComplex f) :
    SeparatedTuples.IsC1c (ComplexTestFunctions.rePart f) :=
  ⟨hf.1.1, IsCompact.of_isClosed_subset hf.2 (isClosed_tsupport _) (tsupport_rePart_subset f)⟩
theorem imPart_isC1c {f : ComplexValued} (hf : IsC1cComplex f) :
    SeparatedTuples.IsC1c (ComplexTestFunctions.imPart f) :=
  ⟨hf.1.2, IsCompact.of_isClosed_subset hf.2 (isClosed_tsupport _)
    (tsupport_imPart_subset f)⟩
open Classical in
def singleSpan (f : ComplexValued) (hf : IsC1cComplex f) : FormalSpan :=
  if ComplexTestFunctions.imPart f = 0 then
    basisVec (R4TupleForms.singleTuple (ComplexTestFunctions.rePart f) (rePart_isC1c hf))
  else basisVec (R4TupleForms.singleTuple (ComplexTestFunctions.rePart f) (rePart_isC1c hf)) +
    Complex.I • basisVec (R4TupleForms.singleTuple (ComplexTestFunctions.imPart f) (imPart_isC1c hf))
def complexObservable {a : ℝ} (f : ComplexValued) (U : GaugeField a) : ℂ :=
  (InfiniteLattice.smearedEnergy (ComplexTestFunctions.rePart f) U : ℝ) +
    Complex.I * (InfiniteLattice.smearedEnergy (ComplexTestFunctions.imPart f) U : ℝ)
end YangMills.Construction.ComplexTupleComponents
