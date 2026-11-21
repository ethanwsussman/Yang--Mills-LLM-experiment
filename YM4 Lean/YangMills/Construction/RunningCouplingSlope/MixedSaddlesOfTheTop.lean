import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators Matrices
variable {L n k : ℕ}
def saddleMatrix (a : ℝ) (U : Edge L n k 0 → ComplexMatrix2) :
    Matrix (Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k)
      (Fin 3 × PositiveEdge L n k 0 ⊕ Fin 3 × PositiveEdge L n k k) ℂ :=
  Matrix.fromBlocks (Matrix.of (rescaledOperators L n k U).X) (meanQTranspose L n k U)
    (Matrix.of (meanKernelQ L n k U)) (-Matrix.of (noiseCovariance a L n k U k))
def ghostMatrix (U : Edge L n k 0 → ComplexMatrix2) :
    Matrix (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k)
      (Fin 3 × Vertex L n k 0 ⊕ Fin 3 × Vertex L n k k) ℂ :=
  Matrix.fromBlocks (Matrix.of (rescaledOperators L n k U).Delta)
    (Matrix.of (rescaledOperators L n k U).Rt)
    (Matrix.of (meanKernelR L n k U)) 0
end YangMills.Construction.RunningCouplingSlope
end
