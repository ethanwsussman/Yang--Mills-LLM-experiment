import YangMills.Construction.RegionSequence.CellWeightedDistLemmas
import YangMills.Construction.RegionSequence.CoordPathWeight
import YangMills.Construction.RegionSequence.PartitionConsequences
import YangMills.Construction.Torus.CubePartitionProperties
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.RegionSequence
open YangMills.Construction.Torus
namespace CoordPath
theorem continuous_pointAt (S : ℝ) (s : TorusSegment 4) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.RegionSequence.CellDist.continuous_pointAt <;> assumption
variable (𝒮 : NestedRegions)
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_zero : 𝒮.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem isPartitionLevel_of_le {m : ℕ} (hm : m ≤ 𝒮.s) : 𝒮.IsPartitionLevel m := by apply _root_.YangMills.Construction.RegionSequence.PartitionConsequences.isPartitionLevel_of_le_s <;> assumption
theorem Ω_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 𝒮.s) : 𝒮.Ω b ⊆ 𝒮.Ω a := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.Ω_antitone <;> assumption
theorem lOneLength_nonneg (sg : TorusSegment 4) : 0 ≤ sg.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem chainWeight_nonneg (Γ : List (TorusSegment 4)) : 0 ≤ 𝒮.chainWeight Γ := by apply _root_.YangMills.Construction.RegionSequence.WeightedDist.chainWeight_nonneg <;> assumption
end CoordPath
end YangMills.Construction.RegionSequence
