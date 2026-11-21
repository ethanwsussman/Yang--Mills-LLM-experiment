import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def BackgroundGaugeMapsInColourCoeffs : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
      [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)],
      EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
        (∀ (B : edgeFormSpace L n k 0) t,
          toPauliCoeffs (restrictToPositiveEdges (iterCovariantDerivLinear L n k U B :
              Edge L n k k → Matrices.ComplexMatrix2)) t =
            ∑ ι, ((finestMesh L k)⁻¹ : ℂ) * (rescaledOperators L n k U).Q t ι *
              toPauliCoeffs (restrictToPositiveEdges (B : Edge L n k 0 → Matrices.ComplexMatrix2)) ι) ∧
        (∀ (l : vertexFunctionSpace L n k 0) y,
          toPauliCoeffs (iterAverageLinear L n k U l : Vertex L n k k → Matrices.ComplexMatrix2) y =
            ∑ x, (rescaledOperators L n k U).R y x *
              toPauliCoeffs (l : Vertex L n k 0 → Matrices.ComplexMatrix2) x) ∧
        (∀ (g : vertexFunctionSpace L n k k) x,
          toPauliCoeffs (iterAverageRealTranspose L n k U g : Vertex L n k 0 → Matrices.ComplexMatrix2) x =
            ∑ y, ((finestMesh L k ^ 4 : ℝ) : ℂ) * (rescaledOperators L n k U).Rt x y *
              toPauliCoeffs (g : Vertex L n k k → Matrices.ComplexMatrix2) y) ∧
        ∀ (l : vertexFunctionSpace L n k 0) x,
          toPauliCoeffs (covDiffRealTranspose L n k U
              (covDiffLinear L n k U l) : Vertex L n k 0 → Matrices.ComplexMatrix2) x =
            ∑ x', ((finestMesh L k ^ 2 : ℝ) : ℂ) * (rescaledOperators L n k U).Delta x x' *
              toPauliCoeffs (l : Vertex L n k 0 → Matrices.ComplexMatrix2) x'
end YangMills.Construction.RunningCouplingSlope
end
