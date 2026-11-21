import YangMills.Construction.InfiniteLattice.ImagesOfBondsAndInvariantMeasuresOnATorus
import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
structure IsFiniteOver (Q : AddSubgroup (LatticePoint 1)) : Prop where
  periods_finiteIndex : Γ.periods.FiniteIndex
  finiteIndex_of_le : Q.FiniteIndex
  finite_quotientTorus : Finite Γ.QuotientTorus
  finite_cosets : Finite (Q ⧸ Γ.periods.addSubgroupOf Q)
  finite_quotientLink : Finite Γ.QuotientLink
  finite_quotientPlaquette : Finite Γ.QuotientPlaquette
  index_mul : Γ.periods.index = Q.index * (Γ.periods.addSubgroupOf Q).index
end PeriodSublattice
namespace LocalObservableArray
variable (A : LocalObservableArray) (Γ : PeriodSublattice 1)
structure PartitionsPositive (β t : ℝ) : Prop where
  windowPartition_pos : ∀ (W : LinkWindow 1) (U' : GaugeField 1), 0 < A.windowPartition β t W U'
  tiltedPartition_pos : 0 < A.tiltedPartition Γ β t
structure LiftIsProbability (β t : ℝ) : Prop where
  continuous_lift : Continuous Γ.lift
  injective_lift : Function.Injective Γ.lift
  isProbabilityMeasure_tiltedLift : IsProbabilityMeasure (A.tiltedLiftMeasure Γ β t)
  integral_tiltedLift : ∀ F ∈ continuousLocalFunctions 1,
    ∫ U, F U ∂(A.tiltedLiftMeasure Γ β t) =
      PeriodSublattice.integralOf (A.tiltedMeasure Γ β t) (Γ.periodize F)
end LocalObservableArray
def FiniteTorusPartitionsAndLifts : Prop :=
  ∀ β : ℝ, 0 < β → ∀ Γ : PeriodSublattice 1,
    (∀ Q : AddSubgroup (LatticePoint 1), Γ.periods ≤ Q → Γ.IsFiniteOver Q) ∧
    ∀ A : LocalObservableArray, A.FitsPeriods Γ → ∀ t : ℝ,
      A.PartitionsPositive Γ β t ∧ A.LiftIsProbability Γ β t
end InfiniteLattice
end YangMills.Construction
