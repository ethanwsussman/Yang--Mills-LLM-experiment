import YangMills.Construction.Lattice.AxialGauges
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BoxNest
variable {L m : ℕ}
def shellPoints (q : ℕ) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) (i : ℕ) :
    Set (FourTorus L m) :=
  {p | 1 ≤ i ∧ i ≤ q ∧ p ∈ sublattice L m (J i) ∧ p ∈ P (i - 1) \ P i}
def nestPoints (q : ℕ) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) : Set (FourTorus L m) :=
  ⋃ i, shellPoints q P J i
def rootEntranceBond (r : SignedFrame) (P : ℕ → Set (FourTorus L m)) (J : ℕ → ℤ) :
    Bond L m (J 1) :=
  rotatedBoxEntranceBond r (J 1) (sitesIn (P 0))
end YangMills.Construction.PeriodicLattice.BoxNest
