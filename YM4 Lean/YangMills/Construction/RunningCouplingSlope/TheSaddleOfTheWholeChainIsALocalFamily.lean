import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.MatricesOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Conventions
def SaddlePointMatrixIsLocal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        (P : PauliCoordinates L n k) (y y' : Vertex L n k k) (τ τ' : LevelTriple L n k),
        TripleSupportedInCell y τ → TripleSupportedInCell y' τ' →
        tripleNormSq τ ≤ 1 → tripleNormSq τ' ≤ 1 →
        IsLocalAlongCellPair saddlePointIndexCell (fun s t => saddlePointMatrix P a (s • τ + t • τ')) y y' M θ
end YangMills.Construction.RunningCouplingSlope
end
