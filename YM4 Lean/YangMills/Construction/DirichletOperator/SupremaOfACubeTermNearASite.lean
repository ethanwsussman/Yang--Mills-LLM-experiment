import YangMills.Construction.DirichletOperator.LeibnizRulesAndHolderSeminorms
import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (levelSpacing)
open LeibnizHolder (supBondOn supTensorOn)
open ApproxInverseScales (blockLowerBound outerCube)
namespace NearSiteSuprema
variable {𝒮 : NestedRegions} {M : ℕ}
def nearCube (Q : LevelCube 𝒮 M) (y : 𝒮.Point) : Set Q.system.setting.Point :=
  cubeHalfSide (Q.system.embed y) (4 * 𝒮.levelScale y)
end NearSiteSuprema
end YangMills.Construction
