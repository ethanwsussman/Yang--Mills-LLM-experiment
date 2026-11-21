import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FineLaplacianIsLocallyHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k 0)],
        IsLocallyHolomorphicFamily tripleCoordIndexCell fineIndexCell fineIndexCell
          (fun w : TripleCoordIndex L n k → ℂ => ((finestMesh L k ^ 2 : ℝ) : ℂ) •
            (Matrix.of (rescaledOperators L n k (complexChainPoint w).fine).Delta :
              Matrix (Fin 3 × Vertex L n k 0) (Fin 3 × Vertex L n k 0) ℂ))
          ρ C r
end YangMills.Construction.RunningCouplingSlope
end
