import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.AveragingOnPart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def IsAverageFormedOnRegion {k : ℕ} (Ω₀ : Set (FourTorus L m)) (c : BondAtLevel L m K k) : Prop :=
  (bondsInside (refinedBlock k c.source ∪ refinedBlock k c.target) :
      Set (BondAtLevel L m K 0)) ⊆ bondsInside Ω₀
def regionBlockField (k : ℕ) (Ω₀ : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K k) : Matrices.ComplexMatrix2 :=
  blockFieldAtLevel (Averaging.smoothingRadius L) k (extendByOne (bondsInside Ω₀) U) c
end PeriodicLattice
end YangMills.Construction
