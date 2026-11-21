import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefectsProof
import YangMills.Construction.DirichletOperator.BoundsOfTheBracketOnALocalTorus
import YangMills.Construction.DirichletOperator.TransfersOfTheIndicatorOfACube
import YangMills.Construction.RegionSequence.GradientAdjointsOnTorus
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.FirstTypeCubeLocalPart
open YangMills.Construction.PartitionCubes YangMills.Construction.LocalTorusBracket
section Lengths
variable {S : ℝ}
theorem supNorm_sub_comm (a b : PeriodicTorus 4 S) : supNorm (a - b) = supNorm (b - a) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
end Lengths
section Inner
variable {𝒯 : RegionSequence.NestedRegions}
theorem bondInner_comm (f g : 𝒯.FineBond → ℝ) : bondInner f g = bondInner g f := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem finite_fineBond (hT : TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end Inner
section Constants
end Constants
section Cube
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem scale_pos (𝒮 : RegionSequence.NestedRegions) (k : ℕ) : 0 < 𝒮.scale k := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_succ (𝒮 : RegionSequence.NestedRegions) (n : ℕ) :
    𝒮.scale (n + 1) = (𝒮.L : ℝ) * 𝒮.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
abbrev cubePartitionOnTorus (Q : LevelCube 𝒮 M) : Q.system.setting.Point → ℝ :=
  Q.system.transferFn Q.partitionFn
structure FirstTypeData (Q : LevelCube 𝒮 M) (c : ℝ) : Prop where
  torus : Q.TransfersToTorus
  part : Q.PartitionTransfers
  push : Q.IndicatorTransfers
  props : Q.FirstTypeProperties
  bounded : CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c (mollifyRadius 𝒮 M Q.level) Q.partitionFn
  one_le : 1 ≤ c
  floor : 𝒮.L ^ 5 ≤ M
  lengths : TorusLengthsStatement
variable {Q : LevelCube 𝒮 M} {c : ℝ}
namespace FirstTypeData
theorem scale_eq (H : FirstTypeData Q c) (k : ℕ) : Q.system.setting.scale k = 𝒮.scale k := by
  simp only [RegionSequence.NestedRegions.scale, H.torus.L_eq, H.torus.ξ_eq]
theorem supNorm_self (H : FirstTypeData Q c) (x : 𝒮.Point) : supNorm (x - x) = 0 := by
  rw [sub_self]
  exact (H.lengths 4 𝒮.side 𝒮.side_pos).1.supNorm_zero
theorem L_ge_thirteen (_ : FirstTypeData Q c) : (13 : ℝ) ≤ 𝒮.L := by
  exact_mod_cast 𝒮.thirteen_le_L
theorem pow_five_le (H : FirstTypeData Q c) : (𝒮.L : ℝ) ^ 5 ≤ M := by
  exact_mod_cast H.floor
theorem sq_mul_le (H : FirstTypeData Q c) : 72 * (𝒮.L : ℝ) ^ 2 ≤ M := by
  have h₁ := H.L_ge_thirteen
  have h₂ : (72 : ℝ) ≤ (𝒮.L : ℝ) ^ 3 := by
    have : (13 : ℝ) ^ 3 ≤ (𝒮.L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h₁ 3
    linarith
  have h₃ : 72 * (𝒮.L : ℝ) ^ 2 ≤ (𝒮.L : ℝ) ^ 3 * (𝒮.L : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h₂ (by positivity)
  have h₄ := H.pow_five_le
  nlinarith
theorem one_le_M (H : FirstTypeData Q c) : (1 : ℝ) ≤ M := by
  have h₁ := H.sq_mul_le
  have h₂ := H.L_ge_thirteen
  nlinarith
theorem mollifyRadius_pos (H : FirstTypeData Q c) : 0 < mollifyRadius 𝒮 M Q.level := by
  have h₁ := H.one_le_M
  have h₂ := H.L_ge_thirteen
  have hξ := scale_pos 𝒮 Q.level
  unfold mollifyRadius cubeSide
  have hM : (0 : ℝ) < M := by linarith
  have hL : (0 : ℝ) < 𝒮.L := by linarith
  exact div_pos (mul_pos hM hξ) (mul_pos (by norm_num) hL)
theorem mem_strictPts_of_thicken (H : FirstTypeData Q c) {x : 𝒮.Point}
    (hx : x ∈ Q.thicken (5 / 6)) : x ∈ Q.strictPts :=
  (H.torus.isometry_ball x hx x (by
    rw [H.supNorm_self]
    have := scale_pos 𝒮 (Q.level + 1)
    linarith)).1
theorem thicken_mono (H : FirstTypeData Q c) : Q.thicken (1 / 6) ⊆ Q.thicken (5 / 6) :=
  fun x hx => by
    have h : supSetDist {x} Q.supp ≤ ENNReal.ofReal (1 / 6 * mollifyRadius 𝒮 M Q.level) := hx
    have hr := H.mollifyRadius_pos
    exact h.trans (ENNReal.ofReal_le_ofReal (by linarith))
theorem embed_injOn (H : FirstTypeData Q c) : InjOn Q.system.embed Q.strictPts :=
  H.props.embed_bijective.injOn
theorem supNorm_le_embed (H : FirstTypeData Q c) {x x' : 𝒮.Point} (hx : x ∈ Q.strictPts)
    (hx' : x' ∈ Q.strictPts) :
    supNorm (x - x') ≤ supNorm (Q.system.embed x - Q.system.embed x') := by
  obtain ⟨p, hp, rfl⟩ := H.props.cover_bijective.surjOn hx
  obtain ⟨p', hp', rfl⟩ := H.props.cover_bijective.surjOn hx'
  rw [H.props.embed_cover p hp, H.props.embed_cover p' hp', H.props.local_supLength p hp p' hp']
  exact H.props.supLength_le p hp p' hp'
theorem exists_preimage_near (H : FirstTypeData Q c) {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6))
    {y : Q.system.setting.Point}
    (hy : supNorm (Q.system.embed x - y) ≤ 2 * 𝒮.scale (Q.level + 1)) :
    ∃ x' ∈ Q.strictPts, Q.system.embed x' = y ∧
      supNorm (x - x') ≤ 2 * 𝒮.scale (Q.level + 1) := by
  have hξ := scale_pos 𝒮 (Q.level + 1)
  obtain ⟨x', h₁, rfl⟩ := H.torus.ball_surj x hx y (by linarith)
  exact ⟨x', h₁, rfl, (H.supNorm_le_embed (H.mem_strictPts_of_thicken hx) h₁).trans hy⟩
theorem anchor_eq_source (H : FirstTypeData Q c) (b : Q.system.setting.FineBond) :
    ((Q.system.setting.anchor b : Q.system.setting.FineSite) : Q.system.setting.Point) =
      (b.source : Q.system.setting.Point) := by
  have h0 : Q.system.setting.Ω 0 = univ := H.torus.cube_setting.full_below 0 (Nat.zero_le _)
  simp [RegionSequence.NestedRegions.anchor, h0]
end FirstTypeData
section Bracket
variable (H : FirstTypeData Q c)
  (F : BracketProperties Q.level (cubePartitionOnTorus Q) (c * (mollifyRadius 𝒮 M Q.level)⁻¹)
    (4 * (c * (mollifyRadius 𝒮 M Q.level)⁻¹ ^ 2)))
include H F
end Bracket
section Linear
variable [Finite 𝒮.FineBond]
end Linear
section Bounds
variable (H : FirstTypeData Q c)
  (F : BracketProperties Q.level (cubePartitionOnTorus Q) (c * (mollifyRadius 𝒮 M Q.level)⁻¹)
    (4 * (c * (mollifyRadius 𝒮 M Q.level)⁻¹ ^ 2)))
include H
include F
end Bounds
end Cube
end YangMills.Construction.FirstTypeCubeLocalPart
