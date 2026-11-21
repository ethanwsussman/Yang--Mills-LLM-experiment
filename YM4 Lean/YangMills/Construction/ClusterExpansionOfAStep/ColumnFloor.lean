import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfCores
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CoreColumns
def nearGap (L r : ℕ) : ℕ := 10 * r / L + 1
def ColumnFloorExists : Prop :=
  ∀ (c rt : ℝ) (L : ℕ), 0 < c → 0 < rt → 0 < L → ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x →
    1 ≤ c * x ∧ 8 * columnConstant rt (nearGap L (TorusLumps.clusterRange x)) ≤ Real.exp (2 * c * x)
end YangMills.Construction.CoreColumns
end
