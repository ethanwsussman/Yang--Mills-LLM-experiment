import YangMills.Construction.Lattice.PreparedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ScaleLabel
variable {L m K m' k : ℕ} {c : ℕ → ℕ}
def absorbedDomain (r : ℕ) (x : ℕ → ℝ) (S : ScaleLabel L m K m' c k)
    (Q : Set (Set (FourTorus L m))) (j : ℕ) : Set (FourTorus L m) :=
  S.trimmedDomain r x Q j ∪ ⋃₀ Q
end YangMills.Construction.PeriodicLattice.ScaleLabel
end
