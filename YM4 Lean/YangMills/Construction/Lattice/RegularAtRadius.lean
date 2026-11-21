import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsRegularWithRadius (r : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsRegularField r K k Ω U
end PeriodicLattice
end YangMills.Construction
