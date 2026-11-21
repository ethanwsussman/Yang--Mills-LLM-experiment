import YangMills.Construction.DirichletOperator.FunctionsNearACubeReadOnItsTorusProof
import YangMills.Construction.DirichletOperator.InequalitiesOnCubesOfTheFirstKindProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.SmallBallIsometry
section Norms
variable {S : ℝ}
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem supNorm_sub_comm (a b : PeriodicTorus 4 S) : supNorm (a - b) = supNorm (b - a) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem supNorm_sub_le_add (a b c : PeriodicTorus 4 S) :
    supNorm (a - c) ≤ supNorm (a - b) + supNorm (b - c) := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.supNorm_sub_le <;> assumption
end Norms
variable {𝒮 : NestedRegions} {M : ℕ}
theorem levelScale_le_scale_succ {y : 𝒮.Point} {n : ℕ}
    (h : y ∈ 𝒮.centresAt n ∨ y ∈ 𝒮.centresAt (n + 1)) :
    𝒮.levelScale y ≤ 𝒮.scale (n + 1) := by
  have hi : 𝒮.level y ≤ n + 1 := by
    rcases h with h | h
    · exact (Nat.sInf_le h).trans (Nat.le_succ n)
    · exact Nat.sInf_le h
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  change (𝒮.L : ℝ) ^ ((𝒮.level y : ℕ) : ℤ) * 𝒮.ξ ≤ (𝒮.L : ℝ) ^ ((n + 1 : ℕ) : ℤ) * 𝒮.ξ
  rw [zpow_natCast, zpow_natCast]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hi) 𝒮.ξ_pos.le
structure CubeSetup (Q : LevelCube 𝒮 M) : Prop where
  transfer : Q.TransfersToTorus
  props : Q.FirstTypeProperties
  proj : Torus.ProjectionFacts 4 𝒮.side
  scale_succ_pos : 0 < 𝒮.scale (Q.level + 1)
  eight_mul_le : 8 * 𝒮.scale (Q.level + 1) ≤ 𝒮.side / 2
variable {Q : LevelCube 𝒮 M}
theorem mem_strictPts_of_mem_thicken (H : CubeSetup Q) {s : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6)) :
    s ∈ Q.strictPts := by
  refine (H.transfer.isometry_ball s hs s ?_).1
  rw [sub_self, supNorm_eq_norm, norm_zero]
  have := H.scale_succ_pos
  positivity
theorem exists_lift_near (H : CubeSetup Q) {q : Fin 4 → ℝ} (hq : q ∈ Q.liftedOpenCube)
    (hs : torusProj 4 𝒮.side q ∈ Q.thicken (5 / 6)) {x : 𝒮.Point}
    (hx : supNorm (x - torusProj 4 𝒮.side q) ≤ 4 * 𝒮.scale (Q.level + 1)) :
    ∃ p ∈ Q.liftedOpenCube, torusProj 4 𝒮.side p = x ∧ ‖q - p‖ ≤ 4 * 𝒮.scale (Q.level + 1) := by
  have F := H.props
  have hx' : supNorm (torusProj 4 𝒮.side q - x) ≤ 4 * 𝒮.scale (Q.level + 1) := by
    rwa [supNorm_sub_comm]
  obtain ⟨hin, hsup, -⟩ := H.transfer.isometry_ball _ hs x hx'
  obtain ⟨p, hp, rfl⟩ := F.cover_bijective.surjOn hin
  refine ⟨p, hp, rfl, ?_⟩
  rw [F.embed_cover q hq, F.embed_cover p hp, F.local_supLength q hq p hp] at hsup
  rw [hsup]
  exact hx'
end PartitionCubes.SmallBallIsometry
end YangMills.Construction
