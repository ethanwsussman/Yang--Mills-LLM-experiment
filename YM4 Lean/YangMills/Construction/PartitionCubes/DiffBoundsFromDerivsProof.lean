import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.PartitionCubes.FiniteDifference
abbrev unitVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
theorem torusProj_add (S : ℝ) (a b : Fin 4 → ℝ) :
    torusProj 4 S (a + b) = torusProj 4 S a + torusProj 4 S b := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem exists_torusProj_eq {S : ℝ} (x : PeriodicTorus 4 S) : ∃ v, torusProj 4 S v = x := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusProj_surjective <;> assumption
end YangMills.Construction.PartitionCubes.FiniteDifference
