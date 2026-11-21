import YangMills.Construction.DirichletOperator.CellsCommonToACubeAndItsTorusProof
import YangMills.Construction.RegionSequence.WeightedDistTriangleProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.RegionSequence.CellDist
section TorusFacts
variable {S : ℝ}
theorem mem_cubeAt_iff {c p : Torus.PeriodicTorus 4 S} {r : ℝ} :
    p ∈ Torus.cubeAt c r ↔ ‖p - c‖ ≤ r / 2 := by apply _root_.YangMills.Construction.PartitionCubes.CellsTransferProof.mem_cubeAt_iff <;> assumption
theorem continuous_pointAt (s : Torus.TorusSegment 4) : Continuous (s.pointAt S) := by
  refine continuous_pi fun μ => ?_
  have h : Continuous fun τ : ℝ => s.start μ + τ * s.direction μ := by fun_prop
  exact (AddCircle.continuous_mk' S).comp h
theorem isConnected_segmentUnion_singleton (s : Torus.TorusSegment 4) :
    IsConnected (Torus.segmentUnion S [s]) := by
  have e : Torus.segmentUnion S [s] = s.pointAt S '' Icc 0 1 := by
    ext p
    simp only [Torus.segmentUnion, List.mem_singleton, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨_, rfl, τ, hτ, rfl⟩
      exact ⟨τ, hτ, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨s, rfl, τ, hτ, rfl⟩
  rw [e]
  exact (isConnected_Icc zero_le_one).image _ (continuous_pointAt s).continuousOn
theorem lengthWithin_singleton (s : Torus.TorusSegment 4) (X : Set (Torus.PeriodicTorus 4 S)) :
    Torus.lengthWithin [s] X =
      s.lOneLength * (volume {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ X}).toReal := by
  simp [Torus.lengthWithin]
theorem lOneLength_nonneg (s : Torus.TorusSegment 4) : 0 ≤ s.lOneLength :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
end TorusFacts
variable (𝒮 : NestedRegions)
theorem cast_L_pos : (0 : ℝ) < 𝒮.L := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_add (n j : ℕ) : 𝒮.scale (n + j) = (𝒮.L : ℝ) ^ j * 𝒮.scale n := by
  simp only [NestedRegions.scale, Torus.scaleSpacing]
  push_cast
  rw [zpow_add₀ (cast_L_pos 𝒮).ne', zpow_natCast, zpow_natCast]
  ring
theorem exists_side_eq_mul_scale {n : ℕ} (hn : n ≤ 𝒮.s) : ∃ N : ℤ, 𝒮.side = N * 𝒮.scale n := by apply _root_.YangMills.Construction.PartitionCubes.SharedCellsProof.side_mem_zmultiples_scale <;> assumption
variable {𝒮}
theorem Ω_antitone {a b : ℕ} (h : a ≤ b) : 𝒮.Ω b ⊆ 𝒮.Ω a := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.regions_antitone <;> assumption
theorem level_spec {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    𝒮.level y ≤ 𝒮.s ∧ y ∈ Torus.spacingLattice 4 𝒮.side (𝒮.scale (𝒮.level y)) ∧
      y ∈ 𝒮.shellOf (𝒮.level y) := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hne : {k | y ∈ Torus.shellSites 𝒮.L 𝒮.ξ 𝒮.Ω k}.Nonempty := ⟨n, hyn⟩
  obtain ⟨-, h1, h2⟩ := Nat.sInf_mem hne
  exact ⟨(Nat.sInf_le hyn).trans hn, h1, h2⟩
theorem chainWeight_nonneg (Γ : List (Torus.TorusSegment 4)) : 0 ≤ 𝒮.chainWeight Γ := by apply _root_.YangMills.Construction.RegionSequence.WeightedDist.chainWeight_nonneg <;> assumption
end YangMills.Construction.RegionSequence.CellDist
