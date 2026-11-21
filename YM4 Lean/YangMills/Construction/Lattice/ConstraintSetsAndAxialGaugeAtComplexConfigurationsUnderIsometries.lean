import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometriesPreserveComplexConstraintSetsAndAxialGauge : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      (∀ (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
        ComplexConstraintSetCovariant σ K k Ω) ∧
      ∀ (K k : ℕ), k < K → i ≤ levelDepth K (k + 1) → ∀ (P'' : Set (SiteAtLevel L m K (k + 1)))
        (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
        IsComplexBlockAxialGauge K k (sitePreimage σ.symm '' P'')
            (transportGaugeField σ V) ↔ IsComplexBlockAxialGauge K k P'' V
end YangMills.Construction.PeriodicLattice
