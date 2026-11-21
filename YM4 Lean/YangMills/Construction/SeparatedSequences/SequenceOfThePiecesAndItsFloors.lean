import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedSequences.PieceChain
open PeriodicLattice
variable {L m : ℕ} (S : ScaleData)
def sideInUnits (L m : ℕ) : ℝ := S.toUnits L (torusSide L m)
variable {S}
end YangMills.Construction.SeparatedSequences.PieceChain
