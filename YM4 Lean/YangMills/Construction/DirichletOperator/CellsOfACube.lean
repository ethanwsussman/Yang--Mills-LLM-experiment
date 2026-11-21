import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
open Classical in
def LevelCube.cellPoints (Q : LevelCube 𝒮 M) : Set Q.system.setting.Point :=
  if Q.IsSecondType then (spacingLattice 4 Q.system.setting.side Q.system.setting.ξ : Set _)
  else Q.system.setting.allCentres
open Classical in
def LevelCube.cellSide (Q : LevelCube 𝒮 M) (w : Q.system.setting.Point) : ℝ :=
  if Q.IsSecondType then Q.system.setting.scale 0 else Q.system.setting.levelScale w
open Classical in
def LevelCube.cellAt (Q : LevelCube 𝒮 M) (w : Q.system.setting.Point) : Set Q.system.setting.Point :=
  if Q.IsSecondType then cubeAt w (Q.system.setting.scale 0) else Q.system.setting.cellOf w
def LevelCube.restrictBondsToCell (Q : LevelCube 𝒮 M) (w : Q.system.setting.Point)
    (v : Q.system.setting.FineBond → ℝ) : Q.system.setting.FineBond → ℝ :=
  restrictBonds (Q.cellAt w) v
def LevelCube.restrictTensorToCell {r : ℕ} (Q : LevelCube 𝒮 M) (w : Q.system.setting.Point)
    (J : Q.system.setting.Tensor r) : Q.system.setting.Tensor r :=
  restrictTensor (Q.cellAt w) J
def LevelCube.thickened (Q : LevelCube 𝒮 M) (X : Set Q.system.setting.Point) :
    Set Q.system.setting.Point :=
  {x | supSetDist {x} X ≤ ENNReal.ofReal (2 * 𝒮.scale (Q.level + 1))}
end PartitionCubes
end YangMills.Construction
