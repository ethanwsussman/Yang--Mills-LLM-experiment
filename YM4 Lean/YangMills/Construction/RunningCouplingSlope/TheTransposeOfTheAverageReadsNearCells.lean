import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def SmoothingTransposeIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
        [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
        IsLocallyHolomorphicFamily tripleCoordIndexCell
          (fun p : Fin 3 × Tower.Vertex L n k k => levelVertexCell p.2) fineIndexCell
          (fun w : TripleCoordIndex L n k → ℂ => ((Tower.finestMesh L k ^ 4 : ℝ) : ℂ) •
            (Matrix.of (Tower.rescaledOperators L n k (complexChainPoint w).fine).Rt :
              Matrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k k) ℂ))
          ρ C r
end YangMills.Construction.RunningCouplingSlope
end
