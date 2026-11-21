import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.Lattice.GreenOperatorsOfCubes
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CornerGreen
open YangMills.Construction.RegionSequence.NestedRegions
variable {S : RegionSequence.NestedRegions} {M : ℕ}
abbrev cubeTorus (Q : PartitionCubes.LevelCube S M) : RegionSequence.NestedRegions :=
  Q.system.setting
def levelMesh (Q : PartitionCubes.LevelCube S M) : ℝ := S.scale Q.level
def cutoffWeight (Q : PartitionCubes.LevelCube S M) (α : ℝ) (ζ : (cubeTorus Q).FineSite → ℝ) : ℝ :=
  holderSite α (levelMesh Q) ζ + supSite ζ
def expDecay (Q : PartitionCubes.LevelCube S M) (δ : ℝ) (w w' : (cubeTorus Q).Point) : ℝ :=
  Real.exp (-δ * Q.torusDist w w')
def rate (L : ℕ) : ℝ := min 1 (CubeCovering.cubeDecayRate L)
end YangMills.Construction.CornerGreen
