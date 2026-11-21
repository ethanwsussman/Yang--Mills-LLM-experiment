import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def TopSecondVariationIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k 0)]
        [Fintype (Fin 3 × Tower.Vertex L n k k)]
        (Q : PauliCoordinates L n k),
        ∃ K : (TripleCoordIndex L n k → ℂ) → Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ,
          IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell levelFormIndexCell K
            ρ C r ∧
          ∀ᶠ x : TripleCoordIndex L n k → ℝ in 𝓝 0, ∀ η η' : LevelForms L n k,
            (((Tower.traceFinsumPairing (Tower.restrictToPositiveEdges ((tripleOfCoords Q x).2.2 : Tower.Edge L n k k → Matrices.ComplexMatrix2))
                (topSecondVariation (pointOfCoords Q x) η η')).re : ℝ) : ℂ) =
              complexifyCoords (Q.formCoords η) ⬝ᵥ
                (K (complexifyCoords x)).mulVec (complexifyCoords (Q.formCoords η'))
end YangMills.Construction.RunningCouplingSlope
end
