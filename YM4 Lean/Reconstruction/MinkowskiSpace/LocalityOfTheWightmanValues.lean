import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
noncomputable section
namespace YangMills.Construction.WightmanLocality
def WightmanLocalityStatement : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) (℘ C : ℝ),
    FieldForms.IsBoundedFieldForm E Ω A ℘ C → FieldForms.IsEuclidean E Ω A →
    ∀ (b : ℕ) (j : Fin b) (f : Fin (b + 1) → WightmanTheory.TestFn),
      (∀ x ∈ tsupport (f j.castSucc).1, ∀ y ∈ tsupport (f j.succ).1,
        y - x ∈ MinkowskiSpace.spacelikeSet) →
      RealPointVectors.wightmanFunctional E Ω A (b + 1)
          (RealPointVectors.tensorVal fun i => (f (Equiv.swap j.castSucc j.succ i)).1) =
        RealPointVectors.wightmanFunctional E Ω A (b + 1) (RealPointVectors.tensorVal fun i => (f i).1)
end YangMills.Construction.WightmanLocality
