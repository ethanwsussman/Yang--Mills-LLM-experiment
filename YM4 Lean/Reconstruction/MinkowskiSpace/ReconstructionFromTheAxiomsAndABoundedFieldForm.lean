import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Reconstruction.MinkowskiSpace.WightmanTheoryOfAEuclideanFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open FieldForms ConfigSpace ProjectionMeasures FormsOperators OneLoopNotation ComplexHilbert
  WightmanTheory FieldFormHilbert FormReconstruction
section BoundedForm
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
structure ReconstructionProperties (S : FlatSequence) : Prop where
  exists_theory : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (T : HermitianScalarTheory H), IsTheoryOf T S
  nonexpanding : S.TimeShiftNonexpanding
  shiftOp_spec : ∀ t : ℝ, 0 ≤ t → S.IsTimeShiftContraction t (S.timeShiftOp t)
  semigroup : SesquilinearForms.IsOpSemigroup S.timeShiftFamily
  strongCont : SesquilinearForms.StronglyContinuous S.timeShiftFamily
  symmetric : ∀ t : NNReal, IsSymmetricOp (S.timeShiftFamily t)
  contractive : ∀ t : NNReal, SesquilinearForms.IsContractive (S.timeShiftFamily t)
  mapsTo_positiveTimeSubspace : ∀ t : ℝ, 0 ≤ t → ∀ χ ∈ S.positiveTimeSubspace,
    S.timeShiftOp t χ ∈ S.positiveTimeSubspace
  exists_subspaceTheory : ∃ (T' : HermitianScalarTheory S.positiveTimeSubspace)
    (J : UnitaryMap S.positiveTimeSubspace (tensorHilbert E Ω A))
    (T : HermitianScalarTheory (tensorHilbert E Ω A)),
    IsTheoryOf T' S ∧ IsVacuumClass S T'.vacuum ∧
      HamiltonianSemigroupRestricts S T' ∧ IsReconstructionIsometry E Ω A S J ∧
      IsFormTheory E Ω A T ∧ IsUnitaryImage J.symm T T'
end BoundedForm
def ReconstructionFromBoundedForm : Prop :=
  ∀ S : FlatSequence, IsLinearFunctionalSeq S → IsContinuousSeq S →
    IsEuclidInvariant S → IsOSPositive S → IsPermSymmetric S →
    ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p c : ℝ),
      IsBoundedFieldForm E Ω A p c → RepresentsSequence E Ω A S →
      ReconstructionProperties E Ω A S
end YangMills.Construction.MinkowskiSpace
end
