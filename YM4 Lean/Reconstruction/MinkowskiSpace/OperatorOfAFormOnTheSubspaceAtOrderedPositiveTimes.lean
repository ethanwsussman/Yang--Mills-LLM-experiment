import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open FieldForms ConfigSpace ProjectionMeasures FormsOperators OneLoopNotation ComplexHilbert
  WightmanTheory FieldFormHilbert FormReconstruction
def ReconstructionIsometryExists : Prop :=
  ∀ S : FlatSequence, IsLinearFunctionalSeq S → IsContinuousSeq S →
    IsEuclidInvariant S → IsOSPositive S → IsPermSymmetric S →
    ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p c : ℝ),
      IsBoundedFieldForm E Ω A p c →
      RepresentsSequence E Ω A S →
      ∃ J : UnitaryMap S.positiveTimeSubspace (tensorHilbert E Ω A),
        IsReconstructionIsometry E Ω A S J
end YangMills.Construction.MinkowskiSpace
end
