import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
open Filter
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open OperatorCalculus OneLoopNotation Tower.UnitLatticeL2 Matrices
namespace Tower.AbelianFieldDensity
open SectorDecomposition in
def LogSectorsAndDensity : Prop :=
  (∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (z : ℝ), 0 < z →
    LogShiftedProps H z ∧ LogCommIntertwiner H H' z) ∧
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    (∀ e : PeriodicOperators.PosEdge L 0 0,
      ∃! p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = e) ∧
    (∀ t : ComplexMatrix2, IsWeightMatrix t → t ∈ ComplexMatrix2.traceless) ∧
    (∀ X ∈ ComplexMatrix2.traceless, ∀ v : VectorL2 L 1, ∀ x : FullSpace.Vertex L 0 0,
      ofCoords (vertexTensor v X) x = v x 0 • X) ∧
    (∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords (edgeTensor v X) (FullSpace.forwardEdge x μ) = v x μ • X) ∧
    (∀ f : L2Field (FullSpace.Vertex L 0 0),
      ofCoords (pointwiseStar f) = fieldStar (ofCoords f)) ∧
    (∀ f : L2Field (PeriodicOperators.PosEdge L 0 0),
      ofCoords (pointwiseStar f) = fieldStar (ofCoords f)) ∧
    LogEqIntegralIoi (L2Field (FullSpace.Vertex L 0 0)) z ∧
    LogEqIntegralIoi (L2Field (PeriodicOperators.PosEdge L 0 0)) z ∧
    (∀ N' : ℕ, 1 ≤ N' → LogEqIntegralIoi (VectorL2 L N') z) ∧
    LogRestrictsToSector (vertexTensor (L := L)) z ∧
    LogRestrictsToSector (edgeTensor (L := L)) z ∧
    TraceSplitsBySector (vertexTensor (L := L)) (vertexPos L) ∧
    TraceSplitsBySector (edgeTensor (L := L)) (edgePos L) ∧
    TraceStarConj (vertexTensor (L := L)) (vertexPos L) ∧
    TraceStarConj (edgeTensor (L := L)) (edgePos L) ∧
    (∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, DensityDefined (L := L) z θ →
      AbelianLogDecomposition (vertexTensor (L := L)) (vertexPos L) z
          (laplacianOp θ) ∧
        AbelianLogDecomposition (edgeTensor (L := L)) (edgePos L) z
          (massiveOp θ)) ∧
    (∀ u ∈ FullSpace.gaugeGroupAt L 0 0,
      DensityInvariance z (gaugeVertexFn (L := L) u) (gaugeEdgeFn (L := L) u) 0) ∧
    ∀ n : Fin 4 → ℤ, DensityInvariance z (vertexShift (L := L) n) (edgeShift (L := L) n) n
end Tower.AbelianFieldDensity
end YangMills.Construction
end
