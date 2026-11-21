import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open PeriodicLattice
namespace EquivariantMaps
theorem compactGaugeGroup_subset_complexGaugeGroup : compactGaugeGroup ⊆ complexGaugeGroup :=
  fun _ h => (Matrix.mem_specialUnitaryGroup_iff.mp h).2
end EquivariantMaps
end YangMills.Construction
