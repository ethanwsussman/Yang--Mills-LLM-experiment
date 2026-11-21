import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometriesPreserveCells : Prop :=
  ∀ (L m : ℕ) (i j : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → i ≤ j → PreservesCells σ j
end YangMills.Construction.PeriodicLattice
