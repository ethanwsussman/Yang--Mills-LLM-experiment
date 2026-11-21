import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def continuedTowerField_isometry_statement : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      ∀ (ε εBar rB ξ : ℝ), 0 < ε → 0 < εBar → 0 < rB → 0 < ξ →
        ∀ (K n e r : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m)),
          IsChainFromIndex K n i Ω' → IsSeparatedChain K e r 0 n Ω' →
          (∃ c : ℤ, i ≤ c ∧ c ≤ levelDepth K 0 ∧ IsPartitionRegion c X) →
          determiningSetSupport Ω' ⊆ X →
          ∀ W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2,
            ContinuedTowerFieldCovariant σ ε εBar rB ξ K n Ω' X W U ∧
            (IsTorusTranslation σ →
              (HasContinuedTowerField ε εBar rB ξ K n Ω' X W U ↔
                HasContinuedTowerField ε εBar rB ξ K n (imageChain σ Ω')
                  (σ '' X) (transportGaugeField σ W) (transportGaugeField σ U)))
end YangMills.Construction.PeriodicLattice
end
