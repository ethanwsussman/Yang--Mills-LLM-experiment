import YangMills.Construction.DirichletOperator.ChangeOfTheDomainInTheGaugeTermProof
import YangMills.Construction.DirichletOperator.ChangedLongitudinalSourceAtTheCellsOfACubeProof
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace LongDifferenceTransfer
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeDivergence.norm_unitStep_le <;> assumption
theorem thicken_mono (Q : LevelCube 𝒮 M) (hr : 0 ≤ mollifyRadius 𝒮 M Q.level) {a b : ℝ}
    (h : a ≤ b) : Q.thicken a ⊆ Q.thicken b := fun _ hx =>
  le_trans hx (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h hr))
theorem target_sub_source (b : 𝒮.FineBond) :
    (b.target : 𝒮.Point) - (b.source : 𝒮.Point) = (unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.Point) := by
  change ((b.source : 𝒮.Point) + (unitStep 4 𝒮.side 𝒮.ξ b.dir : 𝒮.Point)) - _ = _
  abel
theorem torusProj_liftedCentre (Q : LevelCube 𝒮 M) :
    torusProj 4 𝒮.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
theorem coe_mapSite (Q : LevelCube 𝒮 M) (F : Q.FirstTypeProperties)
    (hξ : Q.system.setting.ξ = 𝒮.ξ) (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by apply _root_.YangMills.Construction.CubeDivergence.coe_mapSite <;> assumption
end LongDifferenceTransfer
end YangMills.Construction
