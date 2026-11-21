import YangMills.Construction.Lattice.SourcesWithoutConstantPart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def flatSourceClass (L m : ℕ) (M ϱ : ℝ) : Set (FourTorus L m → ℂ) :=
  {v | FlatNormLT M ϱ v}
end PeriodicLattice
end YangMills.Construction
