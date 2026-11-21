import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def minimalFieldOn (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun U =>
    U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω B V
end PeriodicLattice
end YangMills.Construction
