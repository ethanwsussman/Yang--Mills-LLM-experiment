import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubesProof
import YangMills.Construction.DirichletOperator.CubeTransfersAreAdjointProof
import YangMills.Construction.DirichletOperator.SourcesOfATermOfACubeAtTheCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence PartitionCubes ApproxInverseScales
open LeibnizHolder (supBondOn supTensorOn)
open CubeTorus (levelSpacing tensorModulusAt torusSetting)
open CubeOperators (RegularityConstants IsCubeScale chosenConstants)
open EnlargedCubeBounds (EnlargedKernelBounds)
open CellSources (CellDecomposition termAtCell)
open NearSiteSuprema (nearCube)
namespace CubeTermPointwise
section
variable {𝒯 : NestedRegions}
theorem supNorm_target_sub_source (b : 𝒯.FineBond) :
    supNorm ((b.target : 𝒯.Point) - (b.source : 𝒯.Point)) ≤ 𝒯.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
end
variable {𝒮 : NestedRegions} {M : ℕ}
theorem levelSpacing_pos (Q : LevelCube 𝒮 M) : 0 < levelSpacing Q := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.levelSpacing_pos <;> assumption
section
variable {𝒯 : NestedRegions} {ι : Type}
theorem abs_le_tensorModulusAt {r : ℕ} (J : 𝒯.Tensor r) (ν : Fin r → Fin 4) (x : 𝒯.FineBond) :
    |J ν x| ≤ tensorModulusAt J x :=
  le_ciSup (f := fun ν => |J ν x|) (Set.finite_range _).bddAbove ν
end
end CubeTermPointwise
end YangMills.Construction
