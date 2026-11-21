import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def ChainBracketIsLocallyHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)]
        [Fintype (Fin 3 × Vertex L n k k)]
        (P : PauliCoordinates L n k),
        ∃ G : (TripleCoordIndex L n k → ℂ) → Matrix (Fin 3 × Vertex L n k 0) (LevelFormIndex L n k) ℂ,
          IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell fineIndexCell G
            ρ C r ∧
          ∀ᶠ x : TripleCoordIndex L n k → ℝ in 𝓝 0, ∀ (l : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k),
            ((levelPairing (formValues (tripleOfCoords P x).2.1)
                (chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
                  (formValues ξ)) : ℝ) : ℂ) =
              complexifyCoords (fineVertexCoords P l) ⬝ᵥ
                (G (complexifyCoords x)).mulVec (complexifyCoords (P.formCoords ξ))
end YangMills.Construction.RunningCouplingSlope
end
