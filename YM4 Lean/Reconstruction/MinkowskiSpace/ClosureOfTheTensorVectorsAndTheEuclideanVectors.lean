import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors.TensorClosure
open MinkowskiSpace FieldForms OneLoopNotation ProjectionMeasures
def Statement : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (p C : ℝ),
    IsBoundedFieldForm E Ω A p C →
    tensorDomainClosure E Ω A =
        SesquilinearForms.closedLinSpan (euclideanStates E Ω A) ∧
      (∀ (n : ℕ) (φ : Motions.TensorVal ℂ n), φ ∈ WightmanReconstruction.schwartzOfOrder n →
        testState E Ω A n φ ∈ tensorDomainClosure E Ω A) ∧
      ∀ (n : ℕ) (z : Fin (n + 1) → ComplexVec4), (∀ i, MinkowskiSpace.diffCoords z i ∈ futureTube) →
        stateVector E Ω A (n + 1) z ∈ tensorDomainClosure E Ω A
end YangMills.Construction.RealPointVectors.TensorClosure
