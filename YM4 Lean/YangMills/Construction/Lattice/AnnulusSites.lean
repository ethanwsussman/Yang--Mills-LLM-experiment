import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def annulusSites (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) : Set (SiteAtLevel L m K j) :=
  if j < k then sitesIn (Ω j \ Ω (j + 1)) else sitesIn (Ω k)
end PeriodicLattice
end YangMills.Construction
