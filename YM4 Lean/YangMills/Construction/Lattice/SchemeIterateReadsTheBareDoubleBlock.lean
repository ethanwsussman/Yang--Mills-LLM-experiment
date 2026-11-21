import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnUnionsOfBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def IteratedAverageLocality : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K : ℕ, 0 < m → 0 < K →
    ∀ (s : AveragingScheme) (j : ℕ), j ≤ K →
    ∀ (c : BondAtLevel L m K j) (U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
      IsGaugeField complexGaugeGroup (bondsWithin (sitesInBondBlockPair 0 c)).bonds U →
      IsGaugeField complexGaugeGroup (bondsWithin (sitesInBondBlockPair 0 c)).bonds U' →
      (∀ b ∈ (bondsWithin (sitesInBondBlockPair 0 c)).bonds, U b = U' b) →
      (IsIteratedAverageDefinedAt s U j c ↔ IsIteratedAverageDefinedAt s U' j c) ∧
        (IsIteratedAverageDefinedAt s U j c → iteratedAverage s j U c = iteratedAverage s j U' c)
end PeriodicLattice
end YangMills.Construction
