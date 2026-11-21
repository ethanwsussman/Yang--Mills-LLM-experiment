import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.SchemesOfTheOneStepToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def IsBareIterateDefined (s : AveragingScheme) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → BondAtLevel L m K n → Prop
  | 0, _ => True
  | n + 1, c =>
    (∀ b ∈ (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K n)),
        IsBareIterateDefined s U n b) ∧
      IsOneStepAverageFormed s (iteratedAverage s n U) c.positivelyOriented
end YangMills.Construction.PeriodicLattice
end
