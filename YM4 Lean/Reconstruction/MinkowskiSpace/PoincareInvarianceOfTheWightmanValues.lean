import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
noncomputable section
namespace YangMills.Construction.WightmanPoincare
def WightmanPoincareInvariance : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp K) (Ω : K)
    (A : ℝ → OneLoopNotation.BddOp K) (℘ C : ℝ),
    FieldForms.IsBoundedFieldForm E Ω A ℘ C → FieldForms.IsEuclidean E Ω A →
    ∀ (g : WightmanTheory.PoincareElt) (n : ℕ) (φ : TestSpaces.PointTuple (n + 1) → ℂ),
      φ ∈ TestSpaces.schwartzSet (n + 1) →
      MinkowskiSpace.poincarePullback g.1 φ ∈ TestSpaces.schwartzSet (n + 1) ∧
        RealPointVectors.wightmanFunctional E Ω A (n + 1) (MinkowskiSpace.poincarePullback g.1 φ) =
          RealPointVectors.wightmanFunctional E Ω A (n + 1) φ
end YangMills.Construction.WightmanPoincare
