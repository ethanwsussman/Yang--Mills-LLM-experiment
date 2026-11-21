import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfComplexForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ComplexTransport
def RegionHessianCovariance : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), Conventions.IsAdmissibleBlockingFactor L →
    0 < m → -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    ∀ K k : ℕ, -(m : ℤ) < levelDepth K 0 → i ≤ levelDepth K 0 → ∀ i' : ℤ, i ≤ i' → i' ≤ levelDepth K 0 →
      ∀ Ω₀ : Set (FourTorus L m), IsPartitionRegion i' Ω₀ → ∀ ℬ : Set (BondAtLevel L m K 0),
        IsReversalClosed ℬ → bondsInside Ω₀ ⊆ ℬ → RegionHessianTransport σ k Ω₀ ℬ
end YangMills.Construction.PeriodicLattice
