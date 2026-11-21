import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def blockAverageCaseAtBond (ω : ℝ) {n : ℕ} (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (b : BondAtLevel L m K (n + 1)) : BlockAverageCase :=
  blockAverageCase ω W b.positivelyOriented
end PeriodicLattice
end YangMills.Construction
