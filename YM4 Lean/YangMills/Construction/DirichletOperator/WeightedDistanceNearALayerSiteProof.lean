import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import YangMills.Construction.DirichletOperator.WeightedDistanceInACubeProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.WeightedDistNearShell
section SupNorm
variable {S : ℝ}
theorem torusProj_add (v w : Fin 4 → ℝ) :
    torusProj 4 S (v + w) = torusProj 4 S v + torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin 4 → ℝ) :
    torusProj 4 S (v - w) = torusProj 4 S v - torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem supNorm_eq_norm (z : PeriodicTorus 4 S) : supNorm z = ‖z‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_torusProj_le (v : Fin 4 → ℝ) : ‖torusProj 4 S v‖ ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem supSetDist_singleton_le_of_mem {a q : PeriodicTorus 4 S} {A : Set (PeriodicTorus 4 S)}
    (hq : q ∈ A) : supSetDist {a} A ≤ ENNReal.ofReal ‖a - q‖ := by apply _root_.YangMills.Construction.PartitionCubes.CornerShell.supSetDist_singleton_le <;> assumption
end SupNorm
variable {𝒮 : NestedRegions} {M R₁ : ℕ}
theorem scale_pos' (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem le_s_of_mem_centresAt {y : 𝒮.Point} {j : ℕ} (hy : y ∈ 𝒮.centresAt j) : j ≤ 𝒮.s := by
  by_contra h
  rw [𝒮.centresAt_eq_empty_of_lt (by omega)] at hy
  exact hy
end YangMills.Construction.PartitionCubes.WeightedDistNearShell
end
