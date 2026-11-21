import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.BondsWithinSiteSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K i : ℕ}
abbrev coarseSiteBlock (y : SiteAtLevel L m K (i + 1)) : Set (SiteAtLevel L m K i) :=
  sitesInBlock (levelDepth K i) y
abbrev coarseSiteBlockBonds (y : SiteAtLevel L m K (i + 1)) : SymmetricBondSet L m K i :=
  bondsWithin (coarseSiteBlock y)
def IsGaugeFieldNearBlock (y : SiteAtLevel L m K (i + 1)) (ℬ : Set (BondAtLevel L m K i))
    (U : BondAtLevel L m K i → Matrices.ComplexMatrix2) : Prop :=
  IsReversalClosed ℬ ∧ (coarseSiteBlockBonds y).bonds ⊆ ℬ ∧ IsGaugeField complexGaugeGroup ℬ U
def IsLieFieldNearBlock (y : SiteAtLevel L m K (i + 1)) (𝒜 : Set (BondAtLevel L m K i))
    (A : BondAtLevel L m K i → Matrices.ComplexMatrix2) : Prop :=
  (∀ b ∈ 𝒜, b.IsPositivelyOriented) ∧
    (∀ b ∈ (coarseSiteBlockBonds y).bonds, b.IsPositivelyOriented → b ∈ 𝒜) ∧
    ∀ b ∈ 𝒜, A b ∈ Matrices.ComplexMatrix2.traceless
end YangMills.Construction.PeriodicLattice
