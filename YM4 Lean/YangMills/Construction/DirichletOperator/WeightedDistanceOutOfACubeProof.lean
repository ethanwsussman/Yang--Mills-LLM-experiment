import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import YangMills.Construction.DirichletOperator.FunctionsNearACubeReadOnItsTorusProof
import YangMills.Construction.RegionSequence.WeightedDistTriangle
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.WeightedDistFromCube
theorem weightedDist_comm (𝒮 : RegionSequence.NestedRegions) (a b : 𝒮.Point) :
    𝒮.weightedDist a b = 𝒮.weightedDist b a := by
  unfold YangMills.Construction.RegionSequence.NestedRegions.weightedDist
  congr 1
  ext r
  constructor <;> rintro ⟨Γ, h₁, h₂, h₃, h₄⟩ <;> exact ⟨Γ, h₁, h₃, h₂, h₄⟩
theorem supNorm_sub_comm {S : ℝ} (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem scale_succ (𝒮 : RegionSequence.NestedRegions) (n : ℕ) :
    𝒮.scale (n + 1) = (𝒮.L : ℝ) * 𝒮.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
theorem scale_pos (𝒮 : RegionSequence.NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
end YangMills.Construction.PartitionCubes.WeightedDistFromCube
