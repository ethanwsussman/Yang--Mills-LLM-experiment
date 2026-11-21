import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
def BondOrientationDichotomy : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ j : ℤ, -(m : ℤ) < j →
    ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
end YangMills.Construction.PeriodicLattice
