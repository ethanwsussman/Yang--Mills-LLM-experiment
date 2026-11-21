import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Matrices
namespace Tower
def CovariantIteratesAnalyticEntries : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k → j ≤ k →
    ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      (∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒰 fun U =>
          φ (iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) c.1)) ∧
      (∀ (B : edgeFormSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒰 fun U =>
          φ (iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2) y)) ∧
      ∀ (l : vertexFunctionSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒰 fun U =>
          φ (iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2) y)
end Tower
end YangMills.Construction
