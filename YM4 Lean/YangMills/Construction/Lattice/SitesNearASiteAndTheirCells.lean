import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import YangMills.Construction.Lattice.SiteNearnessRadius
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice SeparatedSequences
namespace SeparatedRegions
variable {L m : ℕ} (S : ScaleData)
def IsNearbyTop (Ω : ℕ → Set (FourTorus L m)) (y y' : FourTorus L m) : Prop :=
  y ∈ layerPoints S Ω ∧ y' ∈ layerPoints S Ω ∧
    layerWeightedDist S Ω y y' ≤ ENNReal.ofReal (Lattice.siteNearnessRadius L)
def nearbyCellsUnion (Ω : ℕ → Set (FourTorus L m)) (y : FourTorus L m) : Set (FourTorus L m) :=
  ⋃ y' ∈ {y' | IsNearbyTop S Ω y y'}, cubeOfPoint S Ω y'
end SeparatedRegions
end YangMills.Construction
end
