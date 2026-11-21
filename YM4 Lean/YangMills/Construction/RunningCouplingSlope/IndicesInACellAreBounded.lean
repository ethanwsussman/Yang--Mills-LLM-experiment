import YangMills.Construction.RunningCouplingSlope.MatricesOfTheWholeChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def IndicesPerCellBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∃ m : ℝ, 0 ≤ m ∧ ∀ n : ℕ, 0 < n →
    ∀ y : Tower.Vertex L n k k,
      (∀ j ≤ k, (Nat.card {p : Fin 3 × Tower.Vertex L n k j // levelVertexCell p.2 = y} : ℝ) ≤ m) ∧
      (∀ j ≤ k, (Nat.card {p : Fin 3 × Tower.PositiveEdge L n k j //
        levelVertexCell p.2.1.source = y} : ℝ) ≤ m) ∧
      (Nat.card {q : LevelFormIndex L n k // levelFormIndexCell q = y} : ℝ) ≤ m
end YangMills.Construction.RunningCouplingSlope
end
