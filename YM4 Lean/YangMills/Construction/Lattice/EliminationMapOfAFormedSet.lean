import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def UniqueEliminationClaim : Prop :=
  ∀ (L m K k : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (Γ : Set (BondAtLevel L m K (k + 1))),
      (∀ c ∈ Γ, c.IsPositivelyOriented) → ComplexConstraintDefined V Γ →
      (∀ c ∈ Γ, PivotCoeffInvertible V c) →
      (∀ c ∈ Γ, ∀ c' ∈ Γ, c' ≠ c → ∀ X ∈ complexLieAlgebra,
        linearizedConstraint V (singleBondForm (pivot c') X) c = 0) ∧
      ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
        ∃! B : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsEliminatedForm V Γ A B
end YangMills.Construction.PeriodicLattice
