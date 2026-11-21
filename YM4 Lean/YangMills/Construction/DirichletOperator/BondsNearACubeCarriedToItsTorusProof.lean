import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.FunctionsAndMapsOfTheCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.CubeTorusBonds
section Lengths
variable {S : ℝ}
theorem norm_torusProj_le (w : Fin 4 → ℝ) : ‖torusProj 4 S w‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem torusProj_add (v w : Fin 4 → ℝ) :
    torusProj 4 S (v + w) = torusProj 4 S v + torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_sub (v w : Fin 4 → ℝ) :
    torusProj 4 S (v - w) = torusProj 4 S v - torusProj 4 S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem norm_pi_single_of_nonneg {a : ℝ} (ha : 0 ≤ a) (ν : Fin 4) :
    ‖(Pi.single ν a : Fin 4 → ℝ)‖ = a := by
  rw [Pi.norm_single, Real.norm_of_nonneg ha]
theorem supSetDist_singleton (b : PeriodicTorus 4 S) (C : Set (PeriodicTorus 4 S)) :
    supSetDist {b} C = ⨅ q ∈ C, ENNReal.ofReal (supNorm (b - q)) := by
  simp [supSetDist]
end Lengths
theorem target_coe {S σ : ℝ} (b : LatticeBond 4 S σ) :
    ((b.target : LatticeSite 4 S σ) : PeriodicTorus 4 S) =
      b.source + torusProj 4 S (Pi.single b.dir σ) := rfl
theorem regions_antitone (𝒯 : NestedRegions) {a b : ℕ} (h : a ≤ b) : 𝒯.Ω b ⊆ 𝒯.Ω a := by
  induction b, h using Nat.le_induction with
  | base => exact Subset.rfl
  | succ b _ ih =>
    refine Subset.trans ?_ ih
    by_cases hb : b < 𝒯.s
    · exact 𝒯.Ω_succ_subset b hb
    · rw [𝒯.Ω_eq_empty (b + 1) (by omega)]
      exact empty_subset _
theorem level_scale_pos (𝒯 : NestedRegions) (j : ℕ) : 0 < 𝒯.scale j := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem exists_lift_near_centre (Q : LevelCube 𝒮 M) {x : 𝒮.Point} {r : ℝ}
    (h : ‖x - Q.centre‖ < r) :
    ∃ p : Fin 4 → ℝ, torusProj 4 𝒮.side p = x ∧ ∀ μ, |p μ - Q.liftedCentre μ| < r := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_near_centre <;> assumption
structure PlacedCube (Q : LevelCube 𝒮 M) : Prop where
  props : Q.FirstTypeProperties
  located : ThickenedCubeLocation.Located Q
  typePos : PositionByType.FirstTypePosition Q
  scale_eq : ∀ j : ℕ, Q.system.setting.scale j = 𝒮.scale j
  mem_bonds : ∀ b : Q.system.setting.FineBond, b ∈ Q.system.setting.bonds
  regions_low : ∀ j ≤ Q.level, Q.system.setting.Ω j = univ
  regions_top : Q.system.setting.Ω (Q.level + 2) = ∅
  scale_le_radius : 366 * 𝒮.scale (Q.level + 1) ≤ mollifyRadius 𝒮 M Q.level
  radius_le_side : mollifyRadius 𝒮 M Q.level ≤ cubeSide 𝒮 M Q.level / 78
variable {Q : LevelCube 𝒮 M}
theorem mollifyRadius_pos_of (H : PlacedCube Q) : 0 < mollifyRadius 𝒮 M Q.level := by
  have h₁ := level_scale_pos 𝒮 (Q.level + 1)
  have h₂ := H.scale_le_radius
  linarith
theorem thicken_mono (H : PlacedCube Q) : Q.thicken (2 / 3) ⊆ Q.thicken (5 / 6) := by
  intro x hx
  refine le_trans hx (ENNReal.ofReal_le_ofReal ?_)
  have := mollifyRadius_pos_of H
  linarith
theorem norm_sub_centre_lt (H : PlacedCube Q) {x : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6)) :
    ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level := by
  have h := H.located.near_centre hx
  change supNorm (x - Q.centre) < _ at h
  rwa [supNorm_eq_norm] at h
theorem mem_lattice_of_embed (H : PlacedCube Q) {j : ℕ}
    (hj : j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s)) {x : 𝒮.Point} (hx : x ∈ Q.strictPts)
    (h : Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side (𝒮.scale j)) :
    x ∈ spacingLattice 4 𝒮.side (𝒮.scale j) := by
  have E := H.props.embed_sites j hj
  have h₁ : Q.system.embed x ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale j) : Set 𝒮.Point) ∩ Q.strictPts) := by
    rw [E]
    exact ⟨h, H.props.embed_bijective.mapsTo hx⟩
  obtain ⟨u, ⟨hu, hu'⟩, hue⟩ := h₁
  have : u = x := H.props.embed_bijective.injOn hu' hx hue
  exact this ▸ hu
theorem embed_mem_lattice (H : PlacedCube Q) {j : ℕ}
    (hj : j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s)) {x : 𝒮.Point} (hx : x ∈ Q.strictPts)
    (h : x ∈ spacingLattice 4 𝒮.side (𝒮.scale j)) :
    Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side (𝒮.scale j) := by
  have E := H.props.embed_sites j hj
  have h₁ : Q.system.embed x ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale j) : Set 𝒮.Point) ∩ Q.strictPts) :=
    ⟨x, ⟨h, hx⟩, rfl⟩
  rw [E] at h₁
  exact h₁.1
end PartitionCubes.CubeTorusBonds
end YangMills.Construction
