import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
structure ComplexAverageIsLocalAt (c : BondAtLevel L m K (n + 1)) : Prop where
  mem_domain_iff : ∀ U U' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = U' b) →
      (U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)) ↔
        U' ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)))
  average_eq : ∀ U U' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), U b = U' b) →
      complexBlockAverageOnPositive U c = complexBlockAverageOnPositive U' c
def ComplexAverageIsLocal : Prop :=
  ∀ L m K n : ℕ, Odd L → 13 ≤ L → 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented → ComplexAverageIsLocalAt c
end PeriodicLattice
end YangMills.Construction
