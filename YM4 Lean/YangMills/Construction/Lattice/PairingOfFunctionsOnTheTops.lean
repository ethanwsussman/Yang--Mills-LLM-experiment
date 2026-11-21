import YangMills.Construction.Lattice.SeparatedSequenceInLastUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace SeparatedSequences
variable {L m : ℕ} (S : ScaleData)
def topPointPairing (Ω : ℕ → Set (FourTorus L m))
    (μ μ' : ↥(layerPoints S Ω) → Matrices.ComplexMatrix2) : ℂ :=
  ∑ᶠ y : ↥(layerPoints S Ω),
    ((layerPointMesh S Ω y ^ 4 : ℝ) : ℂ) * Matrices.ComplexMatrix2.halfTrace (μ y * μ' y)
end SeparatedSequences
end YangMills.Construction
