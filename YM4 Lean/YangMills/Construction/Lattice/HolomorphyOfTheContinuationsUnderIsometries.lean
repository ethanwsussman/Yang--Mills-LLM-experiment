import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IdentitiesOfTheCovarianceAtComplexData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ContinuationsUnderIsometriesHolomorphic : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℤ, -(m : ℤ) ≤ i →
    ∀ g ∈ latticeIsometries L m i,
      ∀ (ε ε' ρ : ℝ), 0 < ε → 0 < ε' → 0 < ρ →
        ∀ (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
          IsSeparatedChain K e r 0 k Ω →
          ∀ V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2,
            HasUniqueMinimizerContinuation ε ε' ρ K k Ω V →
            HasUniqueMinimizerContinuation ε ε' ρ K k (imageChain g Ω)
                (datumImage g V) →
              (∃ (_ : Fintype (PositiveBondIn (activeBondSet K k Ω)))
                (_ : Fintype (bondsInside (imageChain g Ω 0) : Set (BondAtLevel L m K 0))),
                IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω) ρ)
                  (fun (B : ActiveFamily L m K k Ω)
                      (c : (bondsInside (imageChain g Ω 0) : Set (BondAtLevel L m K 0))) =>
                    continuedMinimalField ε ε' ρ K k (imageChain g Ω)
                      (datumImage g V) (twistedActiveFamily g V B) c) ∧
                IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω) ρ)
                  (fun (B : ActiveFamily L m K k Ω)
                      (c : (bondsInside (imageChain g Ω 0) : Set (BondAtLevel L m K 0))) =>
                    transportGaugeField g
                      (continuedMinimalField ε ε' ρ K k Ω V B) c)) ∧
              ∀ B ∈ complexFamilyBall (activeBondSet K k Ω) ρ,
                twistedActiveFamily g V B ∈
                  complexFamilyBall (activeBondSet K k (imageChain g Ω)) ρ
end YangMills.Construction.PeriodicLattice
