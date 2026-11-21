import YangMills.Construction.DirichletOperator.BondsNearACubeCarriedToItsTorusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open scoped ENNReal
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.CellsTransferProof
section Lengths
variable {S : ℝ}
theorem exists_lift_abs_eq_norm (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ∀ μ, |v μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_torusProj_le (w : Fin 4 → ℝ) : ‖torusProj 4 S w‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem mem_cubeAt_iff {y p : PeriodicTorus 4 S} {σ : ℝ} :
    p ∈ cubeAt y σ ↔ ‖p - y‖ ≤ σ / 2 := by
  change supNorm (p - y) ≤ σ / 2 ↔ _
  rw [supNorm_eq_norm]
theorem mem_interior_cubeAt (y : PeriodicTorus 4 S) {σ : ℝ} (hσ : 0 < σ) :
    y ∈ interior (cubeAt y σ) := by
  refine mem_interior.2 ⟨Metric.ball y (σ / 2), fun p hp => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity)⟩
  rw [mem_cubeAt_iff, ← dist_eq_norm]
  exact (Metric.mem_ball.1 hp).le
end Lengths
section Centres
variable (𝒯 : NestedRegions)
theorem nested_le_s_of_nonempty {j : ℕ} (h : (𝒯.Ω j).Nonempty) : j ≤ 𝒯.s := by
  by_contra hj
  rw [𝒯.Ω_eq_empty j (by omega)] at h
  exact not_nonempty_empty h
structure CentreData (y : 𝒯.Point) (j : ℕ) : Prop where
  mem_centres : y ∈ 𝒯.allCentres
  level_eq : 𝒯.level y = j
  cellOf_eq : 𝒯.cellOf y = cubeAt y (𝒯.scale j)
  cellOf_subset_Ω : 𝒯.cellOf y ⊆ 𝒯.Ω j
  mem_Ω : y ∈ 𝒯.Ω j
  not_mem_Ω_succ : y ∉ 𝒯.Ω (j + 1)
variable {𝒯}
end Centres
variable {𝒮 : NestedRegions} {M : ℕ}
theorem exists_lift_near_liftedCentre (Q : LevelCube 𝒮 M) {x : 𝒮.Point} {r : ℝ}
    (h : ‖x - Q.centre‖ < r) :
    ∃ p : Fin 4 → ℝ, torusProj 4 𝒮.side p = x ∧ ∀ μ, |p μ - Q.liftedCentre μ| < r := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_near_centre <;> assumption
theorem mem_strictPts_of_norm_lt {Q : LevelCube 𝒮 M} {x : 𝒮.Point}
    (h : ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level) : x ∈ Q.strictPts := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.mem_strictPts_of_norm_lt <;> assumption
structure CubeData (Q : LevelCube 𝒮 M) : Prop where
  embed_add : ∀ p v : Fin 4 → ℝ, (∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level) →
    (∀ μ, |(p + v) μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level) →
    Q.system.embed (torusProj 4 𝒮.side p + torusProj 4 𝒮.side v) =
      Q.system.embed (torusProj 4 𝒮.side p) + torusProj 4 Q.system.setting.side v
  embed_injOn : InjOn Q.system.embed Q.strictPts
  embed_mapsTo : ∀ x ∈ Q.strictPts, Q.system.embed x ∈
    (fun p : Fin 4 → ℝ => (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
      {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
  embed_lattice : ∀ j : ℕ, j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s) →
    Q.system.embed '' ((spacingLattice 4 𝒮.side (𝒮.scale j) : Set 𝒮.Point) ∩ Q.strictPts) =
      (spacingLattice 4 Q.system.setting.side (𝒮.scale j) : Set Q.system.setting.Point) ∩
        (fun p : Fin 4 → ℝ => (torusProj 4 Q.system.setting.side p : Q.system.setting.Point)) ''
          {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
  mem_Ω_succ_iff : ∀ x ∈ Q.strictPts,
    (x ∈ 𝒮.Ω (Q.level + 1) ↔ Q.system.embed x ∈ Q.system.setting.Ω (Q.level + 1))
  scale_eq : ∀ j, Q.system.setting.scale j = 𝒮.scale j
  s_eq : Q.system.setting.s = Q.level + 1
  Ω_eq_univ : ∀ j ≤ Q.level, Q.system.setting.Ω j = univ
  shellCells : ShellCells 𝒮
  torusShellCells : ShellCells Q.system.setting
  near_of_mem_thicken : ∀ x ∈ Q.thicken (5 / 6),
    ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level
  far_of_mem_thicken : 1 ≤ Q.level → ∀ x ∈ Q.thicken (5 / 6),
    ENNReal.ofReal (1 / 6 * mollifyRadius 𝒮 M Q.level) ≤ distToOutside 𝒮 Q.level x
  far_from_base : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
    supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0))
  disjoint_two_up : Q.enlarge 3 ∩ 𝒮.Ω (Q.level + 2) = ∅
  scale_succ_small : 6 * 𝒮.scale (Q.level + 1) ≤ cubeSide 𝒮 M Q.level
  scale_small : 𝒮.scale Q.level / 2 < 1 / 6 * mollifyRadius 𝒮 M Q.level
  base_small : 𝒮.ξ / 2 ≤ (M : ℝ) * 𝒮.ξ
  side_pos : 0 < cubeSide 𝒮 M Q.level
variable {Q : LevelCube 𝒮 M}
theorem embed_add_torusProj (H : CubeData Q) {x : 𝒮.Point} {w : Fin 4 → ℝ}
    (h : ‖x - Q.centre‖ + ‖w‖ < cubeSide 𝒮 M Q.level) :
    Q.system.embed (x + torusProj 4 𝒮.side w) =
      Q.system.embed x + torusProj 4 Q.system.setting.side w := by
  have h₀ : ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level - ‖w‖ := by linarith
  obtain ⟨p, rfl, hp⟩ := exists_lift_near_liftedCentre Q h₀
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  refine H.embed_add p w (fun μ => by linarith [hp μ]) fun μ => ?_
  have e : (p + w) μ - Q.liftedCentre μ = (p μ - Q.liftedCentre μ) + w μ := by
    simp only [Pi.add_apply]
    ring
  have h₁ : |w μ| ≤ ‖w‖ := by simpa using norm_le_pi_norm w μ
  rw [e]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [hp μ])
end PartitionCubes.CellsTransferProof
end YangMills.Construction
