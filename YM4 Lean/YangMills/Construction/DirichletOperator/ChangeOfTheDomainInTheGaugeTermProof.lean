import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorusComparison
noncomputable section
namespace YangMills.Construction.GaugeDomainChange
theorem levelSpacing_pos {𝒮 : RegionSequence.NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M) :
    0 < YangMills.Construction.CubeTorus.levelSpacing Q := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.levelSpacing_pos <;> assumption
end YangMills.Construction.GaugeDomainChange
