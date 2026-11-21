import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.Conventions
def CellLocalKernelNormBound : Prop :=
  ∀ R : ℝ, ∃ N : ℝ, 0 ≤ N ∧ ∀ L n k : ℕ, IsAdmissibleBlockingFactor L → 0 < n →
    ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
      (c : ι → Vertex L n k k) (c' : ι' → Vertex L n k k) (m m' E : ℝ) (A : Matrix ι' ι ℂ),
      0 ≤ m → 0 ≤ m' → 0 ≤ E →
      (∀ y, (Nat.card {q // c q = y} : ℝ) ≤ m) → (∀ y, (Nat.card {p // c' p = y} : ℝ) ≤ m') →
      (∀ p q, ‖A p q‖ ≤ E) → (∀ p q, R < cellDist (c' p) (c q) → A p q = 0) →
      ‖A‖ ≤ N * Real.sqrt (m * m') * E
end RunningCouplingSlope
end YangMills.Construction
end
