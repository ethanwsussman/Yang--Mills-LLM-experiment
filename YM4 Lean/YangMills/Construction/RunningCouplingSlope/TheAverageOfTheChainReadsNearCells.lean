import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import YangMills.Construction.Towers.GaugeDirectionsOnTheUnitLattice
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
variable {L n k : ℕ}
def composedAverageMatrix (z : TripleCoordIndex L n k → ℂ) :
    Matrix (Fin 3 × Vertex L n k k) (Fin 3 × Vertex L n k 0) ℂ :=
  fun p q => toPauliCoeffs (composedCubeAverage (complexChainPoint z) k
    (ofPauliCoeffs (UnitGaugeDirections.basisFunction q))) p
def ComposedAverageIsLocallyHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)]
        [Fintype (Fin 3 × Vertex L n k k)],
        IsLocallyHolomorphicFamily tripleCoordIndexCell fineIndexCell
          (fun p : Fin 3 × Vertex L n k k => levelVertexCell p.2)
          (composedAverageMatrix (L := L) (n := n) (k := k)) ρ C r
end YangMills.Construction.RunningCouplingSlope
end
