import YangMills.Construction.Lattice.HolomorphicIdentitiesUnderIsometries
import Mathlib
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def PlaquetteVariablesCovarianceStatement : Prop :=
  ∃ ε : SignedFrame → Fin 4 → Fin 4 → ℤˣ,
    ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
      Conventions.IsAdmissibleBlockingFactor L → 0 < m →
      -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → PreservesComplexPlaquetteHolonomies ε σ i
end YangMills.Construction.PeriodicLattice
