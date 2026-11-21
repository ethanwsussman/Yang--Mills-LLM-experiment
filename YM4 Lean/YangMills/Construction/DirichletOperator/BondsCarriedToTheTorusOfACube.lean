import YangMills.Construction.DirichletOperator.GeometryOfCubesAndTheWeightedDistance
import YangMills.Construction.PartitionCubes.AveragedBracketMatrix
import YangMills.Construction.PartitionCubes.LapBracketFormulas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
namespace PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
structure LevelCube.TransfersToTorus (Q : LevelCube 𝒮 M) : Prop where
  cube_setting : IsCubeSetting Q.system.setting Q.level
  L_eq : Q.system.setting.L = 𝒮.L
  ξ_eq : Q.system.setting.ξ = 𝒮.ξ
  mem_forms : ∀ v : Q.system.setting.FineBond → ℝ, v ∈ Q.system.forms
  anchor_eq : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) →
    b ∈ 𝒮.bonds ∧ 𝒮.anchor b = b.source
  mapBond_source : ∀ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ Q.strictPts →
    ((Q.system.mapBond b).source : Q.system.setting.Point) = Q.system.embed (b.source : 𝒮.Point)
  mapBond_dir : ∀ b : 𝒮.FineBond, (Q.system.mapBond b).dir = b.dir
  mapBond_injOn : InjOn Q.system.mapBond {b : 𝒮.FineBond | (b.source : 𝒮.Point) ∈ Q.strictPts}
  mapBond_surj : ∀ e : Q.system.setting.FineBond,
    (e.source : Q.system.setting.Point) ∈ Q.system.embed '' Q.thicken (5 / 6) →
      ∃ b : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) ∧ Q.system.mapBond b = e
  mapBond_shiftUp : ∀ (μ : Fin 4) (b : 𝒮.FineBond), (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) →
    Q.system.mapBond (shiftUp μ b) = shiftUp μ (Q.system.mapBond b)
  mapBond_shiftDown : ∀ (μ : Fin 4) (b : 𝒮.FineBond), (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) →
    Q.system.mapBond (shiftDown μ b) = shiftDown μ (Q.system.mapBond b)
  isometry_ball : ∀ x ∈ Q.thicken (5 / 6), ∀ x' : 𝒮.Point,
    supNorm (x - x') ≤ 4 * 𝒮.scale (Q.level + 1) → x' ∈ Q.strictPts ∧
      supNorm (Q.system.embed x - Q.system.embed x') = supNorm (x - x') ∧
      lOneNorm (Q.system.embed x - Q.system.embed x') = lOneNorm (x - x')
  ball_surj : ∀ x ∈ Q.thicken (5 / 6), ∀ y : Q.system.setting.Point,
    supNorm (Q.system.embed x - y) ≤ 4 * 𝒮.scale (Q.level + 1) →
      ∃ x' ∈ Q.strictPts, Q.system.embed x' = y
structure LevelCube.PartitionTransfers (Q : LevelCube 𝒮 M) : Prop where
  transfer_eq : ∀ x ∈ Q.strictPts, Q.system.transferFn Q.partitionFn (Q.system.embed x) = Q.partitionFn x
  exists_of_ne_zero : ∀ y : Q.system.setting.Point, Q.system.transferFn Q.partitionFn y ≠ 0 →
    ∃ x ∈ Q.supp, Q.system.embed x = y
  lipschitz : ∀ c r : ℝ, CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn →
    IsLipschitzAtScale Q.level (c * r⁻¹) (Q.system.transferFn Q.partitionFn)
  laplacian_le : ∀ c r : ℝ, CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn →
    ∀ x : Q.system.setting.FineSite,
      |latticeLaplacian (onSites (Q.system.transferFn Q.partitionFn)) x| ≤ 4 * (c * r⁻¹ ^ 2)
end PartitionCubes
end YangMills.Construction
