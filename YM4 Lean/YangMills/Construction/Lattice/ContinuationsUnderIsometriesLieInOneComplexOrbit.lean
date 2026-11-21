import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IsometricContinuationsInOneComplexOrbit : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      ∀ (ε εBar rB : ℝ), 0 < ε → 0 < εBar → 0 < rB →
        ∀ (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
          IsSeparatedChain K e r 0 k Ω →
          ∀ V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2,
            HasUniqueMinimizerContinuation ε εBar rB K k Ω V₀ →
            HasUniqueMinimizerContinuation ε εBar rB K k (imageChain σ Ω) (datumImage σ V₀) →
              ∀ B ∈ complexFamilyBall (activeBondSet K k Ω) rB,
                InComplexStabilizerOrbit (imageChain σ Ω)
                  (activeBondSet K k (imageChain σ Ω))
                  (continuedMinimalField ε εBar rB K k (imageChain σ Ω)
                    (datumImage σ V₀) (twistedActiveFamily σ V₀ B))
                  (transportGaugeField σ
                    (continuedMinimalField ε εBar rB K k Ω V₀ B))
end YangMills.Construction.PeriodicLattice
