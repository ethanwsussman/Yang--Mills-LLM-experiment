import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FormIsLocallyAGradient : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ θ : ℝ, 0 < θ →
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ A : Tower.edgeFormSpace L n k 0,
      ∃ l : Tower.Vertex L n k k → Tower.vertexFunctionSpace L n k 0,
        ∑ᶠ (y : Tower.Vertex L n k k) (b : Tower.PositiveEdge L n k 0),
          Real.exp (-(θ * cellDist (fineVertexCell b.1.source) y)) *
            (Matrices.ComplexMatrix2.halfTrace
              (((A : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) b.1 -
                  Tower.vertexCoboundary (l y : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) b.1) *
                ((A : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) b.1 -
                  Tower.vertexCoboundary
                    (l y : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) b.1))).re ≤
          C * (backgroundCurvatureNormSq A + Real.exp (-(c * (2 * (L : ℝ) ^ n))) *
            (Tower.edgeFormPairing (A : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
              (A : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)).re)
end YangMills.Construction.RunningCouplingSlope
end
