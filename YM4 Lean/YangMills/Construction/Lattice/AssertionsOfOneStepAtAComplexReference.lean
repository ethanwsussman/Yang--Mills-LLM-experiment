import YangMills.Construction.Lattice.RadiusOfOneStepAtAComplexReference
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
abbrev complexReferenceRadius (L : ℕ) : ℝ := complexReferenceStepRadius L
variable {L m K n : ℕ}
end YangMills.Construction.PeriodicLattice
