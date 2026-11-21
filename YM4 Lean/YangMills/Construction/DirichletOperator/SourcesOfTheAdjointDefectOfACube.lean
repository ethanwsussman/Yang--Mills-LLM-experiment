import YangMills.Construction.DirichletOperator.CommutatorOfTheLongitudinalOperatorOfACube
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
noncomputable section
namespace YangMills.Construction.CubeAdjointDefect
variable {𝒮 : NestedRegions} {M : ℕ}
def cellWeightedSum (L : ℕ) (Q : LevelCube 𝒮 M) (y : 𝒮.allCentres) (J : Q.system.setting.Tensor 1)
    (s : Q.system.setting.FineBond → ℝ) : ℝ :=
  ∑ᶠ w ∈ Q.cellPoints,
    Real.exp (-(CubeOperators.chosenConstants L).δ *
        Q.torusDist (Q.system.embed (y : 𝒮.Point)) w) *
      (𝒮.scale Q.level * supTensor (Q.restrictTensorToCell w J) +
        𝒮.scale Q.level ^ 2 * supBond (Q.restrictBondsToCell w s))
def commutatorSource (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : Q.system.setting.FineBond → ℝ :=
  CubeCommutator.longCommutator Q (Q.system.pullBonds Q.smallCutoff A)
def outerSource (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : Q.system.setting.FineBond → ℝ :=
  Q.system.pullBonds Q.partitionFn
    (longOp (mulBonds (fun x => 1 - Q.smallCutoff x) A))
end YangMills.Construction.CubeAdjointDefect
