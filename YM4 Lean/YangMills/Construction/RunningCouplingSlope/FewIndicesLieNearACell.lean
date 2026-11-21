import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def FewIndicesNearCell : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, ∃ N : ℕ, ∀ᶠ n in atTop,
    ∀ y : Tower.Vertex L n k k,
      Nat.card {q : LevelFormIndex L n k // cellDist y (levelFormIndexCell q) ≤ r} ≤ N ∧
      Nat.card {p : Fin 3 × Tower.PositiveEdge L n k k // cellDist y (topIndexCell p) ≤ r} ≤ N
end YangMills.Construction.RunningCouplingSlope
end
