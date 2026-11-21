import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace SeparatedSequences
variable {L m : ℕ} (S : ScaleData)
def layerLevel (Ω : ℕ → Set (FourTorus L m)) (y : FourTorus L m) : ℕ :=
  sInf {n | n ≤ S.top ∧ ∃ y' ∈ layerLatticeSites S Ω n, (y' : FourTorus L m) = y}
def layerPointMesh (Ω : ℕ → Set (FourTorus L m)) (y : FourTorus L m) : ℝ :=
  S.levelMesh L (layerLevel S Ω y)
end SeparatedSequences
end YangMills.Construction
