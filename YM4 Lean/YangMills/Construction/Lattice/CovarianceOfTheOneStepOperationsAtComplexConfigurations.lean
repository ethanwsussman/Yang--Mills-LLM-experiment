import YangMills.Construction.Lattice.IdentitiesOfComplexOneStepOperations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ComplexTransport
def ComplexStepIsometryCovariance : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    ∀ K k : ℕ, k < K → i ≤ levelDepth K (k + 1) → ∀ Γ : Set (BondAtLevel L m K (k + 1)),
      (∀ c ∈ Γ, c.IsPositivelyOriented) → ∀ V : BondAtLevel L m K k → Matrices.ComplexMatrix2,
        ComplexConstraintData V Γ →
        ComplexConstraintData (transportGaugeField σ V) (orientedImage σ Γ) →
        StepOperationsTransport σ V Γ
end YangMills.Construction.PeriodicLattice
end
