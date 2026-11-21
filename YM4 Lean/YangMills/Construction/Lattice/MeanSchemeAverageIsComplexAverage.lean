import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
structure CentredAverageIsComplexAt (c : BondAtLevel L m K (n + 1)) : Prop where
  shiftAcross_eq : ∀ μ : Fin 4, c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
    ∀ x : SiteAtLevel L m K n, shiftAcross c x = x + (L : ℤ) • unitStep L m (levelDepth K n) μ
  isOneStepAverageFormed_iff : ∀ U : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    IsOneStepAverageFormed .centred U c ↔ U ∈ complexAveragingDomainNearOne c
  localDefect_eq : ∀ U : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    U ∈ complexAveragingDomainNearOne c →
    ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      localDefect .centred U c x = complexCrossingDefect U c x
  oneStepAverage_eq : ∀ U : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    U ∈ complexAveragingDomainNearOne c →
    oneStepAverage .centred U c = complexBlockAverage U c
  oneStepAverage_opposite_eq : ∀ U : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    U ∈ complexAveragingDomainNearOne c →
    oneStepAverage .centred U c.opposite = complexBlockAverage U c.opposite
def CentredAverageEqComplexBlockAverage : Prop :=
  ∀ L m K n : ℕ, Odd L → 13 ≤ L → 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented → CentredAverageIsComplexAt c
end YangMills.Construction.PeriodicLattice
