import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TensorRepContinuity
open MinkowskiSpace FieldForms WightmanTheory FieldFormHilbert ProjectionMeasures FormsOperators
  OneLoopNotation
def StronglyContinuous : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → IsEuclidean E Ω A →
    ∀ U : PoincareElt → UnitaryMap (tensorHilbert E Ω A) (tensorHilbert E Ω A),
      (∀ g, IsPoincareOp E Ω A g (U g)) →
      ∀ ψ : tensorHilbert E Ω A, Continuous fun g => U g ψ
end YangMills.Construction.TensorRepContinuity
end
