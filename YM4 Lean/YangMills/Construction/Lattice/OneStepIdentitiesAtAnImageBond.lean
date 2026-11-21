import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.LinearisedConstraint
import YangMills.Construction.Lattice.MapsOfTheTwistedAction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
structure TransportIdentitiesAt (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (W : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2)
    (c c' : BondAtLevel L m K (k + 1)) : Prop where
  linearized : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
    linearizedConstraint (transportGaugeField σ V) (twistedTransportForm σ V A) c' =
      twistedFormValue σ W (linearizedConstraint V A) c'
  constraint_map : ∀ B : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra B → ConstraintMapDefined V B c →
    ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
    constraintMap (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
      twistedFormValue σ W (constraintMap V B) c'
  pivotCoeff_conj : ∀ X : ↥Matrices.ComplexMatrix2.traceless,
    ∃ Y : ↥Matrices.ComplexMatrix2.traceless, (Y : Matrices.ComplexMatrix2) = pivotCoeff V c X ∧
    pivotCoeff (transportGaugeField σ V) c'
        (twistedLinkMap σ V (pivot c) X : ↥Matrices.ComplexMatrix2.traceless) =
      (twistedLinkMap σ W c Y : ↥Matrices.ComplexMatrix2.traceless)
  invertible_iff : PivotCoeffInvertible V c ↔
    PivotCoeffInvertible (transportGaugeField σ V) c'
  bilinear : ∀ B₁ B₂ : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm complexLieAlgebra B₁ → IsBondForm complexLieAlgebra B₂ →
      constraintBilinear (transportGaugeField σ V)
          (twistedTransportForm σ V B₁) (twistedTransportForm σ V B₂) c' =
        twistedFormValue σ W (constraintBilinear V B₁ B₂) c'
def TransportIdentitiesAtImageBond : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
      (W : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2)
      (c c' : BondAtLevel L m K (k + 1)), c.IsPositivelyOriented → c'.IsPositivelyOriented →
      (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite) →
      V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      transportGaugeField σ V ∈
        (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      W c = complexBlockAverage V c → TransportIdentitiesAt σ V W c c'
end YangMills.Construction.PeriodicLattice
end
