import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.CubeGreenDivergence
variable {𝒮 : NestedRegions} {M : ℕ}
def divForm (Q : LevelCube 𝒮 M) (J : 𝒮.Tensor 1) : Q.system.setting.FineBond → ℝ :=
  Q.system.inv (Q.system.pullBonds Q.partitionFn (divOne J))
end YangMills.Construction.CubeGreenDivergence
