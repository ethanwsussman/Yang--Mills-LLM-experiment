import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedSequences.LevelWeightMinimum
variable (P : BaseParameters)
theorem side_pos : (0 : ℝ) < P.L := by
  have := P.three_le_L
  exact_mod_cast (by omega : 0 < P.L)
theorem levelMeshRatio_pos (n : ℕ) : 0 < P.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
end YangMills.Construction.SeparatedSequences.LevelWeightMinimum
end
