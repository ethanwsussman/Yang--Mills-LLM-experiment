import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
structure LevelFormsBounded (β : ℝ) (ξ : LevelForms L n k) : Prop where
  bottom_le : ∀ b, Matrices.ComplexMatrix2.operatorNorm
    ((ξ.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) b) ≤ β
  level_le : ∀ (i : Fin k) b, Matrices.ComplexMatrix2.operatorNorm
    ((ξ.2 i : Tower.Edge L n k (i + 1) → Matrices.ComplexMatrix2) b) ≤ β
structure IsLocalValueNearCell [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
    (g : (TripleCoordIndex L n k → ℂ) → Matrices.ComplexMatrix2) (ρ K r : ℝ)
    (y y₀ : Tower.Vertex L n k k) : Prop where
  holomorphic : AnalyticOnNhd ℂ g (Metric.ball 0 ρ)
  traceless : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    g w ∈ Matrices.ComplexMatrix2.traceless
  norm_le : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    Matrices.ComplexMatrix2.operatorNorm (g w) ≤ K
  depends_near : ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    ∀ w' ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
    (∀ i, cellDist (tripleCoordIndexCell i) y ≤ r → w i = w' i) → g w = g w'
  eq_zero_of_far : r < cellDist y y₀ →
    ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ, g w = 0
def TransportAndDriftAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k 0)]
        [Fintype (Fin 3 × Tower.Vertex L n k k)]
        (_ : PauliCoordinates L n k) (y₀ : Tower.Vertex L n k k) (ξ : LevelForms L n k) (β : ℝ),
        0 < β → LevelFormsSupportedInCell y₀ ξ → LevelFormsBounded β ξ → ∀ j ≤ k,
          (∀ b : Tower.Edge L n k j, IsLocalValueNearCell
            (fun w => tangentTransport (complexChainPoint w) ξ j b) ρ (C * β) r
            (levelVertexCell b.source) y₀) ∧
          ∀ y : Tower.Vertex L n k j, IsLocalValueNearCell
            (fun w => chainDrift (complexChainPoint w) ξ j y) ρ (C * β) r (levelVertexCell y) y₀
end YangMills.Construction.RunningCouplingSlope
end
