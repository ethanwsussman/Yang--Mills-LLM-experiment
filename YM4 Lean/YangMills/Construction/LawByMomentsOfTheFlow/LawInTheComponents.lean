import YangMills.Construction.HullsInEveryVolume.LimitDefs
import YangMills.Construction.LawByMomentsOfTheFlow.ComponentsOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open WeightedResponses TorusFields
def periodicComponentCumulantStatement : Prop :=
  ForAllHullParameters fun Λ => ∃ C : ℝ, ∀ (K : ℕ) (β : ℝ), couplingWindowTop Λ.stepParams Λ.g ≤ β →
    IsFirstPassage Λ.stepParams (couplingWindowTop Λ.stepParams Λ.g) β K →
    ∀ ν : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K),
      (∃ ms, TorusLimits.IsTorusLimitAlong Λ.stepParams.side K β ν ms) →
    ∀ (p : ℕ), 1 ≤ p → ∀ κ : Kernel (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)
        (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K),
      TorusLimits.IsPeriodicConditionalKernel Λ.stepParams.side K ν p κ →
      ∀ᵐ U ∂ν, ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.β = β →
        ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell (κ U) - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
          C * S.scaleCoupling ^ (-(1 / 10) : ℝ)
end YangMills.Construction.MomentLaw
end
