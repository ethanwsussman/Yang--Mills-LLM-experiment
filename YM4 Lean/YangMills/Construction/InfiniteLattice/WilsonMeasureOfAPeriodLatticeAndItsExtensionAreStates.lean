import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodicGibbsMeasuresAreStates : Prop :=
  ∀ (a β : ℝ), 0 < a → 0 < β → ∀ Γ : PeriodSublattice a,
    0 < Γ.partitionFunction β ∧ Γ.partitionFunction β ≤ 1 ∧
      IsProbabilityMeasure (Γ.gibbsMeasure β) ∧
      IsProbabilityMeasure (Γ.liftedGibbsMeasure β) ∧
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂Γ.liftedGibbsMeasure β = ∫ U, Γ.periodize F U ∂Γ.gibbsMeasure β) ∧
      ∀ γ ∈ Γ.periods, IsSymmetricUnder (Γ.liftedGibbsMeasure β) (shift γ)
end YangMills.Construction.InfiniteLattice
