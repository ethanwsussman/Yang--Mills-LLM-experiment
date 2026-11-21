import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometriesPreservePartitions : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → ∀ j : ℤ, i ≤ j → PreservesPartitionOperations σ j
end YangMills.Construction.PeriodicLattice
