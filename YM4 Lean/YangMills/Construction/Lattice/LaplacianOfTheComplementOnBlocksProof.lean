import YangMills.Construction.Lattice.LaplacianOfTheComplementOnBlocks
import YangMills.Construction.Lattice.SetsOfSitesInEveryDimension
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace ComplementLaplacian
variable {N : ℕ} {ξ : ℝ}
variable {d L j : ℕ} (S : Scales d L j N)
include S in
theorem two_le_period : 2 ≤ N := by
  obtain ⟨k, hk, hN⟩ := S.even_multiple
  have := S.factor_pos
  have h : 1 * 1 ≤ k * L := Nat.mul_le_mul hk this
  rw [hN]
  nlinarith
include S in
theorem fineScale_pos : 0 < fineScale L j := S.fineMesh.h_pos
end ComplementLaplacian
end YangMills.Construction.PeriodicLattice
