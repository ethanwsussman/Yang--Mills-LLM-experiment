import YangMills.Construction.DirichletOperator.GaugeFormOnAScaledLatticeProof
import YangMills.Construction.Lattice.TorusCharacters
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
theorem Mesh.period_pos (s : Mesh N) : (0 : ℝ) < N := by apply _root_.YangMills.Construction.BareDilation.GaugeForm.torusPeriod_pos <;> assumption
end YangMills.Construction.PeriodicLattice
