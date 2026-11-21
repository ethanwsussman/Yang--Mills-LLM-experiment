import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
def LevelCube.nearSet (Q : LevelCube 𝒮 M) (X : Set 𝒮.Point) : Set 𝒮.Point :=
  {x | supSetDist {x} X ≤ ENNReal.ofReal (2 * 𝒮.scale (Q.level + 1))}
def LevelCube.localSet (Q : LevelCube 𝒮 M) (X : Set 𝒮.Point) : Set Q.system.setting.Point :=
  Q.system.embed '' (X ∩ Q.thicken (5 / 6))
def LevelCube.localForm (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) :
    Q.system.setting.FineBond → ℝ :=
  Q.system.pullBonds (indicator (Q.thicken (5 / 6)) fun _ => 1) A
end PartitionCubes
end YangMills.Construction
