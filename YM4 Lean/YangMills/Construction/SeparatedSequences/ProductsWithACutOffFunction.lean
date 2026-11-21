import YangMills.Construction.Lattice.SitesNearASiteAndTheirCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedRegions
namespace SeparatedSequences.CutoffProducts
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def sitesMeetingSet (K : Set (FourTorus L m)) : Set (FourTorus L m) :=
  {y | y ∈ layerPoints S Ω ∧ (nearbyCellsUnion S Ω y ∩ K).Nonempty}
end SeparatedSequences.CutoffProducts
end YangMills.Construction
end
