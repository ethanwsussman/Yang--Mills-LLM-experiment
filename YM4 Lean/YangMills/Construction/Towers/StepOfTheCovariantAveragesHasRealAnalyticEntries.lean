import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def SmoothingStepAnalyticEntries : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
      (∀ (A : edgeFormSpace L n k i) (e : PositiveEdge L n k (i + 1))
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction U fun V =>
          φ (complexSmoothingDeriv V (A : Edge L n k i → Matrices.ComplexMatrix2) e.1)) ∧
      (∀ (A : edgeFormSpace L n k i) (y : Vertex L n k (i + 1))
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction U fun V =>
          φ (contourLogDrift V (A : Edge L n k i → Matrices.ComplexMatrix2) y)) ∧
      ∀ (f : vertexFunctionSpace L n k i) (y : Vertex L n k (i + 1))
          (φ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction U fun V =>
          φ (adjointCubeAverage V (f : Vertex L n k i → Matrices.ComplexMatrix2) y)
end YangMills.Construction.Tower
end
