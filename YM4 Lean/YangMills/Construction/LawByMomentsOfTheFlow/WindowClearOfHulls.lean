import YangMills.Construction.LawByMomentsOfTheFlow.FunctionsOfTheLimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
variable {Λ : MomentParameters}
def MomentPoint.IsClearFrom (S : MomentPoint Λ) (u : ℕ)
    (w : WeightedResponses.MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : Prop :=
  ∀ (u' : ℕ) (hu' : u' ≤ S.data.windowLevel), u ≤ u' → u' ≤ S.lastSeparated + 2 * S.logIndex + 3 →
    Disjoint (S.stateAtLevel u' hu' w).2.1
      (ResponseInTheExpansion.supBall (S.originSite u' (S.sideAtLevel u')) ((S.range : ℝ) ^ 3))
open Classical in
def notClearIndicator (u : ℕ) : SampleObservable Λ := fun S w => if S.IsClearFrom u w then 0 else 1
open Classical in
def clearCurvaturePower (u : ℕ) (z : Fin 4 → ℤ) (μ ν : Fin 4) (q : ℕ) : SampleObservable Λ := fun S w =>
  if hu : u ≤ S.data.windowLevel then
    if S.IsClearFrom u w then
      TorusFields.curvature (S.stateAtLevel u hu w).1 (S.siteAt u z) μ ν ^ (2 * q)
    else 0
  else 0
end YangMills.Construction.MomentLaw
end
