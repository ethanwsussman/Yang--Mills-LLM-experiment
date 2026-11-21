import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices Conventions
namespace PeriodicLattice
def ComplexGaugeAndMinimalFieldCovariance.Statement : Prop :=
  ∀ (L m : ℕ), IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      (∀ j : ℤ, i ≤ j → ComplexGaugeTransformCovariant σ j) ∧
      (∀ (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
        ComplexDatumGaugeCovariant σ K k Ω ∧ ComplexStabilizerCovariant σ K k Ω ∧
          ComplexConstraintSetCovariant σ K k Ω) ∧
      (∀ (K k : ℕ), k < K → i ≤ levelDepth K (k + 1) → ∀ (P'' : Set (SiteAtLevel L m K (k + 1)))
        (V : BondAtLevel L m K k → ComplexMatrix2),
        IsComplexBlockAxialGauge K k (sitePreimage σ.symm '' P'')
            (transportGaugeField σ V) ↔ IsComplexBlockAxialGauge K k P'' V) ∧
      (∀ (ε εBar rB : ℝ), 0 < ε → 0 < εBar → 0 < rB →
        ∀ (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
          IsSeparatedChain K e r 0 k Ω →
          ∀ V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2,
            ContinuedMinimalFieldCovariant σ ε εBar rB K k Ω V₀ ∧
            (IsTorusTranslation σ → (HasUniqueMinimizerContinuation ε εBar rB K k Ω V₀ ↔
              HasUniqueMinimizerContinuation ε εBar rB K k (imageChain σ Ω)
                (datumImage σ V₀)))) ∧
      (∀ (ε εBar rB ξ : ℝ), 0 < ε → 0 < εBar → 0 < rB → 0 < ξ →
        ∀ (K n e r : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m)),
          IsChainFromIndex K n i Ω' → IsSeparatedChain K e r 0 n Ω' →
          (∃ c : ℤ, i ≤ c ∧ c ≤ levelDepth K 0 ∧ IsPartitionRegion c X) →
          determiningSetSupport Ω' ⊆ X →
          ∀ W U : BondAtLevel L m K 0 → ComplexMatrix2,
            ContinuedTowerFieldCovariant σ ε εBar rB ξ K n Ω' X W U ∧
            (IsTorusTranslation σ →
              (HasContinuedTowerField ε εBar rB ξ K n Ω' X W U ↔
                HasContinuedTowerField ε εBar rB ξ K n (imageChain σ Ω')
                  (σ '' X) (transportGaugeField σ W) (transportGaugeField σ U))))
end PeriodicLattice
end YangMills.Construction
end
