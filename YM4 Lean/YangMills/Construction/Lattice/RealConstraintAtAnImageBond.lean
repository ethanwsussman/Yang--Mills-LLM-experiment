import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
structure RealConstraintAtImage (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (k + 1)) : Prop where
  blockAverage_eq : (blockAverage (Averaging.smoothingRadius L) V c : Matrices.ComplexMatrix2) =
    complexBlockAverage V c
  regular_near_image : IsRegularAveragingNear (Averaging.smoothingRadius L) (transportGaugeField σ V) c'
  differentiableAt_logRatioCurve : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm compactLieAlgebra A →
    DifferentiableAt ℝ
      (logRatioCurve (blockAverage (Averaging.smoothingRadius L)) (transportGaugeField σ V) A c') 0
  mem_complexDomain : transportGaugeField σ V ∈
    (complexAveragingDomainNearOne c' : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))
  linearizedConstraint_eq : ∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm compactLieAlgebra A →
    linearizedConstraintReal (Averaging.smoothingRadius L) (transportGaugeField σ V)
        (twistedTransportForm σ V A) c' =
      twistedFormValue σ (blockAverage (Averaging.smoothingRadius L) V)
        (linearizedConstraintReal (Averaging.smoothingRadius L) V A) c'
  constraintMapDefined_iff : ∀ B : BondAtLevel L m K k → Matrices.ComplexMatrix2,
    IsBondForm compactLieAlgebra B →
    (ConstraintMapDefined V B c ↔
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c')
def RealConstraintAtImageStatement : Prop :=
  ∀ (L m K k : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → k < K → i ≤ levelDepth K (k + 1) →
    ∀ (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (k + 1)),
      c.IsPositivelyOriented → c'.IsPositivelyOriented →
      (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite) →
      IsRegularAveragingNear (Averaging.smoothingRadius L) V c →
      (∀ A : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsBondForm compactLieAlgebra A →
        DifferentiableAt ℝ (logRatioCurve (blockAverage (Averaging.smoothingRadius L)) V A c) 0) →
      V ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) →
      RealConstraintAtImage σ V c c'
end YangMills.Construction.PeriodicLattice
