import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
def LevelPartitionBoxNonempty : Prop :=
  ∀ (S : LevelUnitPartition) (X : Set S.Points), IsPartitionBox S.index X →
    (partitionCubesIn S.index X).Nonempty ∧ X.Nonempty
end YangMills.Construction.PeriodicLattice
