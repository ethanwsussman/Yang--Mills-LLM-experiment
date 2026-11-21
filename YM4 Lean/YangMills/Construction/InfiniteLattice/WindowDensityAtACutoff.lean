import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
theorem meshSize_natCast_pos {L : ℕ} (hL : 0 < L) (K : ℕ) : 0 < PeriodicLattice.meshSize L (K : ℤ) := by apply _root_.YangMills.Construction.SourcesAndGluing.meshSize_pos <;> assumption
end YangMills.Construction.InfiniteLattice
