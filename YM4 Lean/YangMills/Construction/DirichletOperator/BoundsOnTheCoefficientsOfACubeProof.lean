import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import YangMills.Construction.DirichletOperator.LeibnizRulesAndHolderSeminorms
import YangMills.Construction.RegionSequence.AvgOpWeightSum
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.LeibnizHolder
open YangMills.Construction.CubeTorus (levelSpacing)
noncomputable section
namespace YangMills.Construction.PartitionCoefficients
variable {𝒮 : NestedRegions} {M : ℕ}
theorem forwardDiff_smul (ν : Fin 4) (a : ℝ) (f : 𝒮.FineSite → ℝ) :
    forwardDiff ν (a • f) = a • forwardDiff ν f := by
  funext x
  simp only [forwardDiff, Pi.smul_apply, smul_eq_mul]
  ring
theorem nestedScale_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem nestedScale_succ (𝒮 : NestedRegions) (n : ℕ) :
    𝒮.scale (n + 1) = (𝒮.L : ℝ) * 𝒮.scale n := by
  have hL : (𝒮.L : ℝ) ≠ 0 := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 𝒮.L ≠ 0)
  simp only [NestedRegions.scale, YangMills.Construction.Torus.scaleSpacing]
  push_cast
  rw [zpow_add_one₀ hL]
  ring
end YangMills.Construction.PartitionCoefficients
