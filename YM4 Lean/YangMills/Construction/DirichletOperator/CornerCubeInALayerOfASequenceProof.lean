import YangMills.Construction.RegionSequence.ShellDecomposition
import YangMills.Construction.DirichletOperator.CellsCarriedToTheLocalTorusProof
import YangMills.Construction.DirichletOperator.SidesOfTheBlocksAtALevel
import YangMills.Construction.DirichletOperator.WhereThePartitionFunctionOfACubeLives
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.PartitionCubes.CornerShell
variable {S : ℝ}
theorem norm_torusProj_le (v : Fin 4 → ℝ) : ‖torusProj 4 S v‖ ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supSetDist_singleton_le {x q : PeriodicTorus 4 S} {B : Set (PeriodicTorus 4 S)} (hq : q ∈ B) :
    supSetDist {x} B ≤ ENNReal.ofReal ‖x - q‖ := by
  rw [← supNorm_eq_norm]
  exact (iInf₂_le x (mem_singleton x)).trans (iInf₂_le q hq)
variable {𝒮 : RegionSequence.NestedRegions} {M R₁ : ℕ}
theorem cubeSide_pos (hsep : IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω) (n : ℕ) :
    0 < cubeSide 𝒮 M n := by
  have hM : 0 < M := by
    have := hsep.blockSize_isPowerGe.1
    have := 𝒮.thirteen_le_L
    omega
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  exact mul_pos (by exact_mod_cast hM) (mul_pos (zpow_pos hL _) 𝒮.ξ_pos)
theorem cubeSide_succ (n : ℕ) :
    cubeSide 𝒮 M (n + 1) = (𝒮.L : ℝ) * cubeSide 𝒮 M n := by
  have hL : (𝒮.L : ℝ) ≠ 0 := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 𝒮.L ≠ 0)
  simp only [cubeSide, RegionSequence.NestedRegions.scale, scaleSpacing]
  push_cast
  rw [zpow_add_one₀ hL]
  ring
end YangMills.Construction.PartitionCubes.CornerShell
end
