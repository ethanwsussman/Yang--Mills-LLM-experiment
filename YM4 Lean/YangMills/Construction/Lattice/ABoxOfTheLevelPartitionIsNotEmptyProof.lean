import YangMills.Construction.Lattice.ABoxOfTheLevelPartitionIsNotEmpty
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
open Set
theorem levelPartitionBox_nonempty : LevelPartitionBoxNonempty := by
  rintro S X ⟨⟨C, hC, hX⟩, ⟨c⟩⟩
  have hne : X.Nonempty := by
    refine ⟨_, c.image_proj ▸ mem_image_of_mem _
      (?_ : c.lower ∈ TorusBox.boxOfIntervals c.lower c.upper)⟩
    exact fun μ _ => ⟨le_rfl, c.lower_le_upper μ⟩
  obtain ⟨x, hxX⟩ := hne
  have hxC : x ∈ ⋃₀ C := hX ▸ hxX
  obtain ⟨Q, hQ, -⟩ := hxC
  exact ⟨⟨Q, hC hQ, hX ▸ subset_sUnion_of_mem hQ⟩, x, hxX⟩
end YangMills.Construction.PeriodicLattice
