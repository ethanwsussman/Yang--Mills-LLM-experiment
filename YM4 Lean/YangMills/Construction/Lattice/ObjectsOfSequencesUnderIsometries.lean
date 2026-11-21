import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometryPreservesChainObjects : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), Conventions.IsAdmissibleBlockingFactor L →
    0 < m → -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → PreservesChainObjects i σ
end YangMills.Construction.PeriodicLattice
end
