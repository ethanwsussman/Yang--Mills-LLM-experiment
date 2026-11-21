import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open FieldForms ConfigSpace ProjectionMeasures FormsOperators OneLoopNotation ComplexHilbert
  WightmanTheory FieldFormHilbert FormReconstruction
open scoped InnerProductSpace in
def SmoothSeqState_inner : Prop :=
  ∀ S : FlatSequence, IsPermSymmetric S →
    ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p c : ℝ),
      IsBoundedFieldForm E Ω A p c →
      RepresentsSequence E Ω A S →
      ∀ Φ Φ' : AdmissibleSeq, IsSmoothPositiveTimeSeq Φ →
        IsSmoothPositiveTimeSeq Φ' →
        ⟪smoothSeqState E Ω A Φ, smoothSeqState E Ω A Φ'⟫_ℂ =
          S.reflectionForm Φ Φ'
end YangMills.Construction.MinkowskiSpace
end
