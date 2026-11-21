import YangMills.Construction.Averaging.DomainOfTheSymmetrisedAverage
import YangMills.Construction.Lattice.CriticalConfigurationsOverABlockField
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
open PeriodicLattice Averaging Matrices
structure AverageAndCriticalTies (T : DerivedConstants) (N : ExternalConstants)
    (L 𝔐 R₁ : ℕ) : Prop where
  smoothingRadius_le : smoothingRadius L ≤ averagingRadiusCap L
  smoothingRadius_properties : ∀ m K : ℕ, 0 < m → 0 < K →
    SymmetrisedDomainProperties L m K (smoothingRadius L)
  criticalRadiusMul_le : criticalRadiusMul L ≤ T.B₃ L
  a₀_le : T.a₀ L 𝔐 R₁ ≤ criticalUniqueRadius L
  a₁_le : T.a₁ L 𝔐 R₁ ≤ criticalExistRadius L (R₁ * 𝔐)
  criticalMinPower_le : (criticalMinPower L : ℝ) ≤ N.productFloor L
  conditions_hold : ∀ B a a' : ℝ, T.B₃ L ≤ B → 0 < a → a ≤ T.a₀ L 𝔐 R₁ → 0 < a' →
    a' ≤ T.a₁ L 𝔐 R₁ → B * a' ≤ a →
    ∀ K m k : ℕ, 0 < K → 0 < m → 1 ≤ k → k ≤ K →
      6 * ((R₁ * 𝔐 : ℕ) : ℝ) ≤ RegionChains.sitesPerAxis L m K k →
      ∀ V : BondAtLevel L m K k → ComplexMatrix2, V ∈ gaugeFieldsAtLevel L m K k →
        CriticalFieldExists B a' K k V ∧ CriticalFieldsOneOrbit a K k V
end YangMills.Construction.ParameterChoice
end
