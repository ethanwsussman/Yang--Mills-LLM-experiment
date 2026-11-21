import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open FieldForms ConfigSpace ProjectionMeasures OneLoopNotation
def EuclideanOfInvariantRepresented : Prop :=
  ∀ S : FlatSequence, IsEuclidInvariant S → IsPermSymmetric S →
    ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p c : ℝ),
      IsBoundedFieldForm E Ω A p c →
      RepresentsSequence E Ω A S → IsEuclidean E Ω A
end YangMills.Construction.MinkowskiSpace
end
