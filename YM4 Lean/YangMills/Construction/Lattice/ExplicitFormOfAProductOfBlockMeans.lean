import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Lattice.TowersOverSetsOfSites
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K k : ℕ}
def BlockHolonomiesDefined (y : SiteAtLevel L m K k)
    (W : (n : ℕ) → BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  ∀ n < k, ∀ z ∈ blockSitesAtLevel (n + 1) y, ∀ x' ∈ sitesInBlock (levelDepth K n) z,
    IsContourHolonomyDefined .centred (W n) z x'
end YangMills.Construction.PeriodicLattice
