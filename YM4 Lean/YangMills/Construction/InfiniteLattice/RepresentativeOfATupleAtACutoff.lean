import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import YangMills.Construction.InfiniteLattice.CutoffLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffRepresentative
open YangMills.Construction.CutoffLattice YangMills.Construction.TupleLists
def centredSmearedField {a : ℝ} (ν : Measure (GaugeField a)) (f : AmbientSpace → ℝ)
    (U : GaugeField a) : ℝ :=
  smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν
def centredProduct (L K : ℕ) (ν : Measure (FieldsAt L K)) (X : TestSpaces.SepTuple)
    (U : FieldsAt L K) : ℝ :=
  ∏ i, centredSmearedField ν (X.2.1 i) U
def centredProductLinear (L K : ℕ) (ν : Measure (FieldsAt L K)) :
    SeparatedTuples.FormalSpan →ₗ[ℂ] FieldsAt L K → ℂ :=
  SeparatedTuples.linearExtend fun X U => ((centredProduct L K ν (ofList X) U : ℝ) : ℂ)
theorem centredProductLinear_basisVec (L K : ℕ) (ν : Measure (FieldsAt L K))
    (X : TestSpaces.SepTuple) (U : FieldsAt L K) :
    centredProductLinear L K ν (SeparatedTuples.basisVec (toList X)) U =
      ((centredProduct L K ν X U : ℝ) : ℂ) := by
  simp [centredProductLinear, SeparatedTuples.linearExtend_basisVec, ofList_toList]
end YangMills.Construction.InfiniteLattice.CutoffRepresentative
