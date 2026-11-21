import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def LevelUnitPartitionEdgesCompactConnected : Prop :=
  ∀ (P : LevelUnitPartition) (E : Set P.Points), P.IsEdge E →
    IsCompact E ∧ IsConnected E ∧ ∀ x, P.IsEdgeEndpoint E x → x ∈ E
end YangMills.Construction.PeriodicLattice
end
