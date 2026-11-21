import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperators
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes
variable {S : NestedRegions} {M : ℕ}
def LevelCube.DecaysFromPoint (Q : LevelCube S M) (L : ℕ) (x' : S.Point) (p : NormExponent)
    (U : ℝ) (u : Q.system.setting.FineBond → ℝ) : Prop :=
  ∀ w ∈ Q.cellPoints,
    (S.scale Q.level ^ 2)⁻¹ * (formCutSpace Q.system.setting).pNorm p
        (restrictBonds (Q.thickened (Q.cellAt w)) u) +
      (S.scale Q.level)⁻¹ * (tensorCutSpace Q.system.setting 1).pNorm p
        (restrictTensor (Q.thickened (Q.cellAt w)) (nablaOne u)) ≤
      U * Real.exp (-(CubeOperators.chosenConstants L).δ *
        Q.torusDist w (Q.system.embed x'))
end YangMills.Construction.PartitionCubes
