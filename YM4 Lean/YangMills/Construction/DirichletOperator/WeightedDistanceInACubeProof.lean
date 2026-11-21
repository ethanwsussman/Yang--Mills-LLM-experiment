import YangMills.Construction.DirichletOperator.LengthsOnACubeOfTheFirstKindProof
import YangMills.Construction.DirichletOperator.UpperRegionOfACubeOfTheFirstKindProof
import YangMills.Construction.PartitionCubes.DiffBoundsFromDerivsProof
import YangMills.Construction.RegionSequence.CoordPathWeight
import YangMills.Construction.RegionSequence.PartitionConsequences
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PartitionCubes.WeightedDistCube
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
variable {𝓡 : NestedRegions} {M : ℕ}
theorem exists_torusProj_eq {S : ℝ} (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p := by apply _root_.YangMills.Construction.PartitionCubes.FiniteDifference.exists_torusProj_eq <;> assumption
theorem torusProj_sub {S : ℝ} (v w : Fin 4 → ℝ) :
    torusProj 4 S (v - w) = torusProj 4 S v - torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.torusProj_sub <;> assumption
theorem lOneNorm_nonneg' {S : ℝ} (p : PeriodicTorus 4 S) : 0 ≤ lOneNorm p := by
  apply Real.sInf_nonneg
  rintro r ⟨v, -, rfl⟩
  positivity
theorem supNorm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem torusProj_liftedCentre (Q : LevelCube 𝓡 M) :
    torusProj 4 𝓡.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
end YangMills.Construction.PartitionCubes.WeightedDistCube
end
