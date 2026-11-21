import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsInTheComponents
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
def componentsReadLimitLawStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (K : ℕ)
    (ν : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K))
    (κ : Kernel (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K))
    (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (j : F.Index) (b₁ b₂ : ℝ), S.data.windowLevel = K →
    TorusLimits.IsTorusLimitAlong Λ.stepParams.side K S.β ν F.exponents →
    TorusLimits.IsPeriodicConditionalKernel Λ.stepParams.side K ν F.period κ →
    F.observables j = bottomProduct c B → (∀ᵐ v ∂F.law, b₁ ≤ F.condMeanAt j v ∧ F.condMeanAt j v ≤ b₂) →
    ∀ᵐ U ∂ν, b₁ ≤ S.centredStateMoment (κ U) c B ∧ S.centredStateMoment (κ U) c B ≤ b₂
end YangMills.Construction.MomentLaw
end
