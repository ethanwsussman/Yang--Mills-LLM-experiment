import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def EliminationWeightAtImageBond : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (k + 1)), c.IsPositivelyOriented →
      c'.IsPositivelyOriented → (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite) →
      V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      transportGaugeField σ V ∈ (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      eliminationWeight (transportGaugeField σ V) c' = eliminationWeight V c
end YangMills.Construction.PeriodicLattice
