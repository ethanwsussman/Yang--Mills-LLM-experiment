import YangMills.Construction.Lattice.ObjectsOfTheLinearPartOfOneStep
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.StraightenedOrder
open BondMaps Matrices
variable {L m K : ℕ}
section Operators
variable [∀ n, Fintype (PositiveBondAtLevel L m K n)]
def stepLinearizationProduct (s : AveragingScheme) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → BondLinearMap (PositiveBondAtLevel L m K 0) (PositiveBondAtLevel L m K n)
  | 0 => LinearMap.id
  | n + 1 => (stepLinearization s (iteratedAverage s n U₀)).comp (stepLinearizationProduct s U₀ n)
def linearizationAtOrder (s : AveragingScheme) (k : ℕ) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondLinearMap (PositiveBondAtLevel L m K 0) (PositiveBondAtLevel L m K k) :=
  ((finestMeshInLevelUnits L k : ℝ) : ℂ) • stepLinearizationProduct s U₀ k
end Operators
end YangMills.Construction.PeriodicLattice.StraightenedOrder
