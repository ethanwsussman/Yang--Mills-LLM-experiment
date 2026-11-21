import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeAsItsSourcesProof
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.PartitionCubes.SecondTypeDefect
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) (v : Fin 4 → ℝ) (hv : ‖v‖ ≤ r) :
    ‖torusProj 4 S v‖ ≤ r := by apply _root_.YangMills.Construction.CubeDivergence.norm_torusProj_le <;> assumption
theorem norm_pi_single_le {r : ℝ} (hr : 0 ≤ r) (ν : Fin 4) :
    ‖(Pi.single ν r : Fin 4 → ℝ)‖ ≤ r := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem norm_unitStep_le {S η : ℝ} (hη : 0 ≤ η) (ν : Fin 4) :
    ‖((unitStep 4 S η ν : LatticeSite 4 S η) : PeriodicTorus 4 S)‖ ≤ η :=
  norm_torusProj_le hη _ (norm_pi_single_le hη ν)
theorem scale_zero_eq : 𝒮.scale 0 = 𝒮.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem scale_pos' (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
end YangMills.Construction.PartitionCubes.SecondTypeDefect
namespace YangMills.Construction.PartitionCubes
end YangMills.Construction.PartitionCubes
end
