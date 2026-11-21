import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LevelUnitPartition
variable (S : LevelUnitPartition)
def domainLinearSize (X : Set S.Points) : ℝ :=
  linearExtent S.params.K S.sideExponent S.level X
def IsDomainFamily (𝒟 : Set (Set S.Points)) : Prop :=
  𝒟 = connectedRegions S.params.L S.params.m S.index ∨
    𝒟 = faceChainConnectedRegions S.params.L S.params.m S.index
end YangMills.Construction.PeriodicLattice.LevelUnitPartition
end
