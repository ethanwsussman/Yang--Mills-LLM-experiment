import YangMills.Construction.RunningCouplingSlope.FamiliesThatReadNearCells
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.LeftChartFields (scalarCoords)
def NearCellFamiliesAreLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ρ C r : ℝ, 0 < ρ → 0 ≤ C → 0 ≤ r →
    ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧ ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
        (c' : ι' → Tower.Vertex L n k k) (F : (Tower.Edge L n k 0 → Matrices.ComplexMatrix2) → Matrix ι' ι ℂ),
        IsLocalNearCells c c' F ρ C r → ∀ z : Fin 4 → ℤ,
          IsLocalAlongBackground c c' (fun s t => F (twoCellResponseForm L n k z (s : ℂ) (t : ℂ))) z M θ
end YangMills.Construction.RunningCouplingSlope
end
