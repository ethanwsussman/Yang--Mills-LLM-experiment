import YangMills.Construction.Lattice.NormaliserAtPositiveArguments
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def softGaugeFixingWeight (t ε : ℝ) (q : Matrices.ComplexMatrix2) : ℝ :=
  (extendedAxialNormalizer t ε)⁻¹ * nearIdentityIndicator ε q * Real.exp (-t * traceDeficit q)
end YangMills.Construction.PeriodicLattice
