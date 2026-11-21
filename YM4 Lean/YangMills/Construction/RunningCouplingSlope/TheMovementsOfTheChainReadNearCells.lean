import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
def coordBasisForm [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
    [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
    [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
    (P : PauliCoordinates L n k) (q : LevelFormIndex L n k) : LevelForms L n k :=
  P.formCoords.symm (Pi.single q 1)
structure IsLocallyHolomorphicNear {I E : Type} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : I → Tower.Vertex L n k k) (y : Tower.Vertex L n k k) (f : (I → ℂ) → E) (ρ C r : ℝ) : Prop where
  holomorphic : AnalyticOnNhd ℂ f (Metric.ball 0 ρ)
  norm_le : ∀ w ∈ Metric.ball (0 : I → ℂ) ρ, ‖f w‖ ≤ C
  depends_near : ∀ w ∈ Metric.ball (0 : I → ℂ) ρ, ∀ w' ∈ Metric.ball (0 : I → ℂ) ρ,
    (∀ i, cellDist (e i) y ≤ r → w i = w' i) → f w = f w'
def BasisTransportAndDriftAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k 0)]
        [Fintype (Fin 3 × Tower.Vertex L n k k)]
        (P : PauliCoordinates L n k) (q : LevelFormIndex L n k),
        (∀ j ≤ k, ∀ b : Tower.Edge L n k j,
          IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell b.source)
            (fun w => tangentTransport (complexChainPoint w) (coordBasisForm P q) j b) ρ C r ∧
          (r < cellDist (levelVertexCell b.source) (levelFormIndexCell q) →
            ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
              tangentTransport (complexChainPoint w) (coordBasisForm P q) j b = 0)) ∧
        ∀ j ≤ k, ∀ y : Tower.Vertex L n k j,
          IsLocallyHolomorphicNear tripleCoordIndexCell (levelVertexCell y)
            (fun w => chainDrift (complexChainPoint w) (coordBasisForm P q) j y) ρ C r ∧
          (r < cellDist (levelVertexCell y) (levelFormIndexCell q) →
            ∀ w ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ,
              chainDrift (complexChainPoint w) (coordBasisForm P q) j y = 0)
end YangMills.Construction.RunningCouplingSlope
end
