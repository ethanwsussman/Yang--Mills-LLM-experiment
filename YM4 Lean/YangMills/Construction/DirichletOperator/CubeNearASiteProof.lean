import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (levelSpacing)
noncomputable section
namespace YangMills.Construction.CubeNearSite
variable {S : NestedRegions}
theorem mem_centresAt_level {x : S.Point} (hx : x ∈ S.allCentres) :
    x ∈ S.centresAt (S.level x) := by
  obtain ⟨n, -, hn⟩ := hx
  exact Nat.sInf_mem (s := {n | x ∈ Torus.shellSites S.L S.ξ S.Ω n}) ⟨n, hn⟩
theorem scale_succ (n : ℕ) : S.scale (n + 1) = (S.L : ℝ) * S.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
theorem scale_pos (n : ℕ) : 0 < S.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem thicken_subset {M : ℕ} (Q : LevelCube S M) : Q.thicken (1 / 6) ⊆ Q.thicken (5 / 6) := by
  intro z hz
  refine le_trans hz (ENNReal.ofReal_le_ofReal ?_)
  have hL : (0 : ℝ) < S.L := by
    have := S.thirteen_le_L
    exact_mod_cast (by omega : 0 < S.L)
  have hr : 0 ≤ mollifyRadius S M Q.level := by
    unfold mollifyRadius cubeSide
    have := scale_pos (S := S) Q.level
    positivity
  linarith
end YangMills.Construction.CubeNearSite
