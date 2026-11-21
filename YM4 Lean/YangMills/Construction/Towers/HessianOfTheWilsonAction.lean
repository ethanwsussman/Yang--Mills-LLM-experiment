import YangMills.Construction.Towers.PartsOfTheHessianOfTheWilsonAction
import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (KernelMatrix compKernel)
section FiniteSide
def scaledEdgeCoboundaryKernel (L n k j : ℕ) :
    KernelMatrix (Fin 3 × PositiveEdge L n k j) (Fin 3 × Face L n k j) :=
  (edgePauliCoordinates L n k j).kernel (vertexCoordinate (Face L n k j)) scaledEdgeCoboundary
def coboundaryAddDefectKernel (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × Face L n k 0) :=
  scaledEdgeCoboundaryKernel L n k 0 + holonomyDefectKernel L n k U
def coboundarySquareKernel (L n k : ℕ) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) :=
  compKernel
    (meshTranspose (finestMesh L k) (finestMesh L k) (coboundaryAddDefectKernel L n k U))
    (compKernel (halfFaceTraceKernel L n k U) (coboundaryAddDefectKernel L n k U))
end FiniteSide
namespace FullSpace
def coboundaryAddDefectKernel (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0)) (Fin 3 × Face L k 0) :=
  scaledEdgeCoboundaryKernel L k 0 + holonomyDefectKernel L k U
def coboundarySquareKernel (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0)) (Fin 3 × PositiveEdge (meshAt L k 0)) :=
  compKernel
    (meshTranspose (finestMesh L k) (finestMesh L k) (coboundaryAddDefectKernel L k U))
    (compKernel (halfFaceTraceKernel L k U) (coboundaryAddDefectKernel L k U))
end FullSpace
namespace WilsonHessian
def DecompositionHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → ∀ a ∈ complexEdgeForms L n k 0,
      (rescaledOperators L n k (remainderGaugeField a)).H =
        coboundarySquareKernel L n k (remainderGaugeField a) +
          curvatureKernel (remainderGaugeField a)) ∧
    ∀ a ∈ FullSpace.complexEdgeForms (meshAt L k 0),
      (FullSpace.rescaledOperators L k (FullSpace.remainderGaugeField a)).H =
        FullSpace.coboundarySquareKernel L k (FullSpace.remainderGaugeField a) +
          FullSpace.curvatureKernel (FullSpace.remainderGaugeField a)
end WilsonHessian
end YangMills.Construction.Tower
end
