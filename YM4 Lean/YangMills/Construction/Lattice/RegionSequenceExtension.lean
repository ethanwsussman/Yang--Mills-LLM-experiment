import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.RegionSequences
variable {L m : ℕ}
def IsTorusRegion (X : Set (FourTorus L m)) : Prop :=
  ∃ i : ℤ, -(m : ℤ) ≤ i ∧ IsPartitionRegion i X
structure IsExtendableTo (K s t : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Prop where
  length_le : s ≤ t
  le_cutoff : t ≤ K
  isRegion : ∀ n ≤ s, IsTorusRegion (Ω n)
  antitone_step : ∀ n < s, Ω (n + 1) ⊆ Ω n
def extendByEmpty (s : ℕ) (Ω : ℕ → Set (FourTorus L m)) : ℕ → Set (FourTorus L m) :=
  fun n => if n ≤ s then Ω n else ∅
end YangMills.Construction.RegionSequences
