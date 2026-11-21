import YangMills.Construction.DirichletOperator.CornerCubeInALayerOfASequenceProof
import YangMills.Construction.DirichletOperator.CubesNearALayerSite
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubesNearShellSite
section Lengths
variable {S : ℝ}
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supSetDist_singleton_le {a q : PeriodicTorus 4 S} {A : Set (PeriodicTorus 4 S)}
    (hq : q ∈ A) : supSetDist {a} A ≤ ENNReal.ofReal ‖a - q‖ := by apply _root_.YangMills.Construction.PartitionCubes.CornerShell.supSetDist_singleton_le <;> assumption
theorem supSetDist_singleton_le_add (A : Set (PeriodicTorus 4 S)) (a b : PeriodicTorus 4 S) :
    supSetDist {a} A ≤ supSetDist {b} A + ENNReal.ofReal ‖a - b‖ := by
  rw [← tsub_le_iff_right]
  refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ?_
  obtain rfl : p = b := hp
  rw [tsub_le_iff_right, supNorm_eq_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine (supSetDist_singleton_le hq).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := norm_add_le (p - q) (a - p)
  rwa [show p - q + (a - p) = a - q by abel] at h
end Lengths
section Levels
variable (𝒮 : NestedRegions)
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_mono {a b : ℕ} (h : a ≤ b) : 𝒮.scale a ≤ 𝒮.scale b := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.scale_mono <;> assumption
theorem topLevel_le_s : topLevel 𝒮 ≤ 𝒮.s := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.topLevel_le <;> assumption
theorem Ω_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 𝒮.s) : 𝒮.Ω b ⊆ 𝒮.Ω a := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.Ω_antitone <;> assumption
variable {𝒮} {M R₁ : ℕ}
end Levels
end YangMills.Construction.PartitionCubes.CubesNearShellSite
