import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import YangMills.Construction.FreeKernel.UnitLatticeHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.ScaledGreen
open InfiniteLattice
open UnitLattice (wordDiff latticeLaplacian latticeForwardDiff latticeBackwardDiff)
variable {d : ℕ} {ξ : ℝ}
def gridPoint (ξ : ℝ) (n : Fin d → ℤ) : GridSite d ξ := ⟨fun μ => (n μ : ℝ) * ξ, n, fun _ => rfl⟩
theorem gridPoint_add (n m : Fin d → ℤ) : gridPoint ξ (n + m) = gridPoint ξ n + gridPoint ξ m := by
  apply Subtype.ext
  funext μ
  simp [gridPoint, add_mul]
theorem gridPoint_sub (n m : Fin d → ℤ) : gridPoint ξ (n - m) = gridPoint ξ n - gridPoint ξ m := by
  apply Subtype.ext
  funext μ
  simp [gridPoint, sub_mul]
theorem gridPoint_single (μ : Fin d) : gridPoint ξ (Pi.single μ (1 : ℤ)) = gridStep μ := by
  apply Subtype.ext
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [gridPoint, gridStep]
  · simp [gridPoint, gridStep, Pi.single_eq_of_ne h]
end YangMills.Construction.FreeKernel.ScaledGreen
