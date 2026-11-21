import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import YangMills.Construction.Towers.PartsOfTheHessianOfTheWilsonAction
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.CriticalBranchResponse
def covariantDifferenceDefect (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × Vertex L n k 0) ℂ :=
  Matrix.of (rescaledOperators L n k (twoSourceBackground L n k w s t)).D -
    Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D
def holonomyDefectAlongBackground (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Face L n k 0) (Fin 3 × PositiveEdge L n k 0) ℂ :=
  Matrix.of (holonomyDefectKernel L n k (twoSourceBackground L n k w s t))
def faceTraceAlongBackground (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Face L n k 0) (Fin 3 × Face L n k 0) ℂ :=
  Matrix.of (halfFaceTraceKernel L n k (twoSourceBackground L n k w s t))
def curvatureAlongBackground (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) ℂ :=
  Matrix.of (curvatureKernel (twoSourceBackground L n k w s t))
def FineOperatorPartsAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)] [Fintype (Fin 3 × Face L n k 0)] [DecidableEq (Fin 3 × Face L n k 0)],
      ∀ w : Fin 4 → ℤ,
        IsLocalAlongBackground colouredVertexCell colouredEdgeCell (covariantDifferenceDefect L n k w) w M θ ∧
        IsLocalAlongBackground colouredEdgeCell colouredFaceCell (holonomyDefectAlongBackground L n k w) w M θ ∧
        IsLocalAlongBackground colouredFaceCell colouredFaceCell (faceTraceAlongBackground L n k w) w M θ ∧
        IsLocalAlongBackground colouredEdgeCell colouredEdgeCell (curvatureAlongBackground L n k w) w M θ
end YangMills.Construction.RunningCouplingSlope
end
