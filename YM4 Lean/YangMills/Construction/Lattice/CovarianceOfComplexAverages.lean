import YangMills.Construction.Lattice.HolomorphicIdentitiesUnderIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplexAveragesCommuteWithIsometries.Statement : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), Conventions.IsAdmissibleBlockingFactor L →
    0 < m → -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → PreservesComplexBlockAverages σ i
end YangMills.Construction.PeriodicLattice
