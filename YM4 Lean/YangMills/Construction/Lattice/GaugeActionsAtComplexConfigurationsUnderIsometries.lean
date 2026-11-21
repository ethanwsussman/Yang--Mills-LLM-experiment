import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ComplexGaugeCovarianceUnderIsometries.Statement : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      (∀ j : ℤ, i ≤ j → ComplexGaugeTransformCovariant σ j) ∧
      ∀ (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
        ComplexDatumGaugeCovariant σ K k Ω ∧ ComplexStabilizerCovariant σ K k Ω
end YangMills.Construction.PeriodicLattice
