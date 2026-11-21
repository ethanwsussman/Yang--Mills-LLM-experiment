import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def IsLowestBlockSite (n : ℕ) (y : Site L m j) (x : Site L m (j + n)) : Prop :=
  ∃ p ∈ blockOffsets L n, x = refinedOffsetSite n y p ∧ ∀ q ∈ blockOffsets L n, ∀ μ, p μ ≤ q μ
def lowestBlockSite (n : ℕ) (y : Site L m j) : Site L m (j + n) :=
  Classical.epsilon (IsLowestBlockSite n y)
end YangMills.Construction.PeriodicLattice
