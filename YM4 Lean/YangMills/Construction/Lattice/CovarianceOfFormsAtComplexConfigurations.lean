import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfComplexForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ComplexTransport
def ComplexTransportCovariance : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    ∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ ℬ : Set (Bond L m j), IsReversalClosed ℬ →
      ComplexTransportIdentities σ ℬ
end YangMills.Construction.PeriodicLattice
