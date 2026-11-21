import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedRegions
variable {L m : ℕ} (S : SeparatedSequences.ScaleData)
def bondSpacing (q : LeveledBond L m S) : ℝ := S.levelMesh L q.1
end YangMills.Construction.SeparatedRegions
