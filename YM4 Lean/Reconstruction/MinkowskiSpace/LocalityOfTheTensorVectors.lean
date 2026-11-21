import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.HilbertSpaceOfTheTensorsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TensorLocality
open MinkowskiSpace FieldForms WightmanTheory FieldFormHilbert ProjectionMeasures OneLoopNotation
def SpacelikeSwapInvariance : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p C : ℝ),
    IsBoundedFieldForm E Ω A p C → IsEuclidean E Ω A →
    ∀ (f h : TestFn) (m : ℕ) (u : Fin m → TestFn),
      (∀ x ∈ tsupport f.1, ∀ y ∈ tsupport h.1, x - y ∈ spacelikeSet) →
      tensorVec E Ω A (Fin.cons f (Fin.cons h u) : Fin (m + 2) → TestFn) =
        tensorVec E Ω A (Fin.cons h (Fin.cons f u) : Fin (m + 2) → TestFn)
end YangMills.Construction.TensorLocality
end
