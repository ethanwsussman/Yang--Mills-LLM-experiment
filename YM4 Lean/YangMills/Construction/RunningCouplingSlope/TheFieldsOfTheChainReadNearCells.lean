import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def LevelFieldsHolomorphicAndLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)]
        [Fintype (Fin 3 × Vertex L n k k)]
        (P : PauliCoordinates L n k),
        (∀ x : TripleCoordIndex L n k → ℝ,
          complexChainPoint (complexifyCoords x) = pointOfCoords P x) ∧
        (∀ m ≤ k, ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
          levelField (complexChainPoint w) m ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup) ∧
        (∀ m ≤ k, ∀ e : Edge L n k m,
          AnalyticOnNhd ℂ (fun w => levelField (complexChainPoint w) m e) (Metric.ball 0 ρ) ∧
          (∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            Matrices.ComplexMatrix2.operatorNorm (levelField (complexChainPoint w) m e - 1) ≤ C * ‖w‖) ∧
          ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            ∀ w' ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell e.source) ≤ r → w i = w' i) →
              levelField (complexChainPoint w) m e = levelField (complexChainPoint w') m e) ∧
        ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
          AnalyticOnNhd ℂ (fun w => meanRadius (levelField (complexChainPoint w) i) c.1)
            (Metric.ball 0 ρ) ∧
          (∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            ‖meanRadius (levelField (complexChainPoint w) i) c.1 - 1‖ ≤ C * ‖w‖) ∧
          ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            ∀ w' ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
            (∀ i', cellDist (tripleCoordIndexCell i') (levelVertexCell c.1.source) ≤ r →
              w i' = w' i') →
              meanRadius (levelField (complexChainPoint w) i) c.1 =
                meanRadius (levelField (complexChainPoint w') i) c.1
end YangMills.Construction.RunningCouplingSlope
end
