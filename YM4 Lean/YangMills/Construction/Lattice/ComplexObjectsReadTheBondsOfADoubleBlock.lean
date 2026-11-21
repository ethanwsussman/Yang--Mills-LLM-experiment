import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K k : ℕ}
structure ComplexDataAgreeOnDoubleBlock (c : BondAtLevel L m K (k + 1))
    (V V' : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop where
  domain_iff : V ∈ complexAveragingDomain c ↔ V' ∈ complexAveragingDomain c
  nearOne_iff : V ∈ complexAveragingDomainNearOne c ↔ V' ∈ complexAveragingDomainNearOne c
  average_eq : complexBlockAverage V c = complexBlockAverage V' c
  holonomy_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K k) y,
      complexMeanContourHolonomy V y x = complexMeanContourHolonomy V' y x
  twist_eq : ∀ A A' : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), A b = A' b) →
      ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), expTwist A V b = expTwist A' V' b
def ComplexDataDeterminedOnDoubleBlock : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K k : ℕ, 0 < m → k < K →
    ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
      ∀ V V' : BondAtLevel L m K k → Matrices.ComplexMatrix2,
        (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), V b = V' b) →
          ComplexDataAgreeOnDoubleBlock c V V'
end YangMills.Construction.PeriodicLattice
end
