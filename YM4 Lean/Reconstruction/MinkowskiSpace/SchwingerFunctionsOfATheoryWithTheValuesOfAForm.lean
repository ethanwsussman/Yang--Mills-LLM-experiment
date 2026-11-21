import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfAEuclideanFieldForm
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TheorySchwinger
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory ProjectionMeasures
  FormsOperators OneLoopNotation ComplexHilbert
def Claim : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ),
    IsBoundedFieldForm E Ω A ℘ C → IsEuclidean E Ω A →
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : HermitianScalarTheory H),
      (∀ (m : ℕ) (f : Fin (m + 1) → TestFn),
        T.wightmanFn f = wightmanFunctional E Ω A (m + 1) (tensorVal fun i => (f i).1)) →
      ∀ S : ConfigSpace.FlatSequence,
        ConfigSpace.IsCLMSequence S →
        (∀ (m : ℕ) (φ : TestSpaces.PointTuple (m + 1) → ℂ),
          φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) :
            Set (TestSpaces.PointTuple (m + 1) → ℂ)) →
          ∀ hφ : φ ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
            S.atSucc m ⟨φ, hφ⟩ = integralSchwinger E Ω A m φ) →
        T.IsSchwingerSequence S ∧
          ∀ m : ℕ, ∃ (q : ℕ) (c : ℝ),
            IsAnalyticContinuationData T S m (vacuumExpectation E Ω A (m + 1)) q c
              (schwinger E Ω A m)
end YangMills.Construction.TheorySchwinger
end
