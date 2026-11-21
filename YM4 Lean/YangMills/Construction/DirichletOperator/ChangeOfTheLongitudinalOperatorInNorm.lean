import YangMills.Construction.DirichletOperator.ApproximateInverseAndLocalDefects
import YangMills.Construction.DirichletOperator.ChangeOfTheDomainInTheGaugeTerm
import YangMills.Construction.DirichletOperator.OperatorsComparingACubeWithTheTorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.CubeTorusComparison
noncomputable section
namespace YangMills.Construction.PartitionCubes.LongChange
variable {𝒮 : NestedRegions} {M : ℕ}
def diffOp (Q : LevelCube 𝒮 M) (v : Q.system.setting.FineBond → ℝ) : 𝒮.FineBond → ℝ :=
  mulBonds Q.smallCutoff (longOp (Q.system.pushBonds Q.partitionFn v)) -
    Q.system.pushBonds Q.smallCutoff (Q.torusLongOp (Q.system.mulTransfer Q.partitionFn v))
end YangMills.Construction.PartitionCubes.LongChange
