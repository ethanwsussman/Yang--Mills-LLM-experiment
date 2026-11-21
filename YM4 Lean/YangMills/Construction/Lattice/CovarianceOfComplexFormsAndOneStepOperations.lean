import YangMills.Construction.Lattice.IdentitiesOfComplexOneStepOperations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
open ComplexTransport
def ComplexFormsAndStepOperationsCovariance.Statement : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    (∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ S : Set (Bond L m j), IsReversalClosed S →
      ComplexTransportIdentities σ S) ∧
    (∀ K k : ℕ, -(m : ℤ) < levelDepth K 0 → i ≤ levelDepth K 0 → ∀ i' : ℤ, i ≤ i' →
      i' ≤ levelDepth K 0 →
      ∀ Ω : Set (FourTorus L m), IsPartitionRegion i' Ω → ∀ S : Set (BondAtLevel L m K 0),
        IsReversalClosed S → bondsInside Ω ⊆ S → RegionHessianTransport σ k Ω S) ∧
    (∀ K k : ℕ, k < K → i ≤ levelDepth K (k + 1) → ∀ C : Set (BondAtLevel L m K (k + 1)),
      (∀ c ∈ C, c.IsPositivelyOriented) →
      StepSidesHolomorphic σ C ∧
      (∀ V : BondAtLevel L m K k → ComplexMatrix2, ComplexConstraintData V C →
        ComplexConstraintData (transportGaugeField σ V) (orientedImage σ C) →
        StepOperationsTransport σ V C) ∧
      (IsTorusTranslation σ → ∀ V : BondAtLevel L m K k → ComplexMatrix2,
        (ComplexConstraintData V C ↔
          ComplexConstraintData (transportGaugeField σ V) (orientedImage σ C)) ∧
        (ComplexConstraintData V C → ∀ A : BondAtLevel L m K k → ComplexMatrix2,
          IsBondForm complexLieAlgebra A → ∀ c ∈ C, ∀ c', IsOrientedImage σ c c' →
            (ConstraintMapDefined V A c ↔
              ConstraintMapDefined (transportGaugeField σ V)
                (twistedTransportForm σ V A) c'))))
end YangMills.Construction.PeriodicLattice
