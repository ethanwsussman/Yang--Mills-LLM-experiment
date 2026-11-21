import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CosineSquaredBump
def cosSqBump (s : ℝ) : ℝ := if |s| ≤ 1 then Real.cos (Real.pi / 2 * s) ^ 2 else 0
theorem cosSqBump_mem_Icc (s : ℝ) : cosSqBump s ∈ Set.Icc (0 : ℝ) 1 := by
  unfold cosSqBump
  split_ifs
  · exact ⟨sq_nonneg _, Real.cos_sq_le_one _⟩
  · exact ⟨le_rfl, zero_le_one⟩
def latticeOfSpacing (w : ℝ) : Set (Fin 4 → ℝ) := {α | ∃ n : Fin 4 → ℤ, ∀ μ, α μ = w * (n μ : ℝ)}
def productBump (w : ℝ) (α x : Fin 4 → ℝ) : ℝ := ∏ μ : Fin 4, cosSqBump ((x μ - α μ) / w)
end YangMills.Construction.CosineSquaredBump
