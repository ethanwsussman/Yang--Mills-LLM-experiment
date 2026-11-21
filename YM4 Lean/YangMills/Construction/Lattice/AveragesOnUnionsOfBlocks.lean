import YangMills.Construction.Lattice.AveragesOfExtensions
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def blockSitesBelow {k : ℕ} (n : ℕ) (Z : Set (SiteAtLevel L m K k)) :
    Set (SiteAtLevel L m K n) :=
  sitesIn (blockUnionAtLevel n Z)
def IsIteratedAverageDefinedAt (s : AveragingScheme)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → BondAtLevel L m K n → Prop
  | 0, _ => True
  | n + 1, c =>
    (∀ b ∈ (bondsWithin (sitesInBondBlockPair n c)).bonds, IsIteratedAverageDefinedAt s U n b) ∧
      IsSchemeAverageDefinedAt s (iteratedAverage s n U) c
end PeriodicLattice
end YangMills.Construction
