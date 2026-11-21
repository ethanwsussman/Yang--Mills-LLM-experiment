import YangMills.Construction.Lattice.TowersAndStepSetsCarriedByIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice Conventions
namespace PeriodicLattice
def IsometriesPreserveMultiShellGluing : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → PreservesMultiShellGluing i σ
end PeriodicLattice
end YangMills.Construction
