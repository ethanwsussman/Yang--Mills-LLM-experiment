import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def GaugeOrbitMapIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k 0)]
        [Fintype (Fin 3 × Tower.Vertex L n k k)]
        (P : PauliCoordinates L n k),
        ∃ G : (TripleCoordIndex L n k → ℂ) → Matrix (LevelFormIndex L n k) (Fin 3 × Tower.Vertex L n k 0) ℂ,
          IsLocallyHolomorphicFamily tripleCoordIndexCell fineIndexCell levelFormIndexCell G
            ρ C r ∧
          ∀ᶠ x : TripleCoordIndex L n k → ℝ in 𝓝 0, ∀ l : Tower.vertexFunctionSpace L n k 0,
            ∃ ξ : LevelForms L n k,
              formValues ξ = gaugeOrbitValues (pointOfCoords P x)
                (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ∧
              complexifyCoords (P.formCoords ξ) =
                (G (complexifyCoords x)).mulVec (complexifyCoords (fineVertexCoords P l))
end YangMills.Construction.RunningCouplingSlope
end
