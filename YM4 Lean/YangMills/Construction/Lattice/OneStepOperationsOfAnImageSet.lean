import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
structure IsometryIntertwinesStepMaps (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (W : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2)
    (S S' : Set (BondAtLevel L m K (k + 1))) : Prop where
  eliminate_comm : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
    eliminate (transportGaugeField σ V) S' (twistedTransportForm σ V A) =
      twistedTransportForm σ V (eliminate V S A)
  pivotLift_comm : ∀ ν : ↥S → Matrices.ComplexMatrix2, (∀ c, ν c ∈ complexLieAlgebra) →
    pivotCorrectionLift (transportGaugeField σ V) S'
        (fun c' : ↥S' => twistedFormValue σ W (Function.extend Subtype.val ν 0) c') =
      fun b' : SupportBond (levelDepth K k) S' =>
        twistedTransportForm σ V (extendForm (pivotCorrectionLift V S ν)) b'
  correction_comm :
    ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) S :
        Set (SupportBond (levelDepth K k) S → Matrices.ComplexMatrix2))] 0,
      linearizingCorrection (transportGaugeField σ V) S'
          (fun b' : SupportBond (levelDepth K k) S' => twistedTransportForm σ V (extendForm B) b') =
        fun c' : ↥S' => twistedFormValue σ W
          (Function.extend Subtype.val (linearizingCorrection V S B) 0) c'
  change_comm :
    ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) S :
        Set (SupportBond (levelDepth K k) S → Matrices.ComplexMatrix2))] 0,
      linearizingChange (transportGaugeField σ V) S'
          (fun b' : SupportBond (levelDepth K k) S' => twistedTransportForm σ V (extendForm B) b') =
        fun b' : SupportBond (levelDepth K k) S' =>
          twistedTransportForm σ V (extendForm (linearizingChange V S B)) b'
def ImageSetIntertwining.Statement : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m), Conventions.IsAdmissibleBlockingFactor L →
    0 < m → -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (W : BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2)
      (S S' : Set (BondAtLevel L m K (k + 1))), (∀ c ∈ S, c.IsPositivelyOriented) →
      (∀ c', c' ∈ S' ↔ ∃ c ∈ S, c'.IsPositivelyOriented ∧
        (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite)) →
      ComplexConstraintDefined V S → (∀ c ∈ S, PivotCoeffInvertible V c) →
      ComplexConstraintDefined (transportGaugeField σ V) S' →
      (∀ c' ∈ S', PivotCoeffInvertible (transportGaugeField σ V) c') →
      (∀ c ∈ S, W c = complexBlockAverage V c) → IsometryIntertwinesStepMaps σ V W S S'
end YangMills.Construction.PeriodicLattice
