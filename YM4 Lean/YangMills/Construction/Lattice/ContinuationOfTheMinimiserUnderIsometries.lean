import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometriesPreserveMinimizerContinuation : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      ∀ (ε εBar rB : ℝ), 0 < ε → 0 < εBar → 0 < rB →
        ∀ (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
          IsSeparatedChain K e r 0 k Ω →
          ∀ V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2,
            ContinuedMinimalFieldCovariant σ ε εBar rB K k Ω V₀ ∧
            (IsTorusTranslation σ → (HasUniqueMinimizerContinuation ε εBar rB K k Ω V₀ ↔
              HasUniqueMinimizerContinuation ε εBar rB K k (imageChain σ Ω)
                (datumImage σ V₀)))
end YangMills.Construction.PeriodicLattice
