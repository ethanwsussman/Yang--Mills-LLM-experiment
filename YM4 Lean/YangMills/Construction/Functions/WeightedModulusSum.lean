import Mathlib
noncomputable section
namespace YangMills.Construction.WeightedModulusSum
structure Weights (n : ℕ) where
  one_le : 1 ≤ n
  c : Fin n → ℝ
  c_pos : ∀ i, 0 < c i
variable {n : ℕ}
def Weights.weightedNorm (w : Weights n) (z : Fin n → ℂ) : ℝ := ∑ i, w.c i * ‖z i‖
def Weights.unitSet (w : Weights n) : Set (Fin n → ℂ) := {z | w.weightedNorm z < 1}
end YangMills.Construction.WeightedModulusSum
