import YangMills.Construction.LawByMomentsOfTheFlow.FarCopiesInALimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion FreeEnergies HullTrees MomentMethod
abbrev LevelCaseFunction (Λ : MomentParameters) (j : ℕ) : Type 1 :=
  (S : MomentPoint Λ) → TorusField (S.sideAtLevel (j + 1)) →
    CaseFunction (S.tower.stage j).toStepSetup (S.sideAtLevel (j + 1))
variable {Λ : MomentParameters}
def caseObservable (j : ℕ) (Φ : LevelCaseFunction Λ j) : SampleObservable Λ := fun S ω =>
  if h : j + 1 ≤ S.data.windowLevel then
    caseLift S.tower j _ (Φ S) (S.sampleAtLevel (j + 1) h ω) else 0
def caseMeanObservable (j : ℕ) (Φ : LevelCaseFunction Λ j) : SampleObservable Λ := fun S ω =>
  if h : j + 1 ≤ S.data.windowLevel then
    caseMeanAtSample S.tower j _ (Φ S) (S.sampleAtLevel (j + 1) h ω) else 0
open Classical in
def clearIndicator (u R : ℕ) : SampleObservable Λ := fun S ω =>
  if h : u ≤ S.data.windowLevel then
    if Disjoint (S.stateAtLevel u h ω).2.1 (supBall (S.originSite u (S.sideAtLevel u)) (R : ℝ)) then 1 else 0
  else 0
def clearStateBoundStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (L : LimitLawAtPoint S) (j Rc Rr : ℕ) (M b : ℝ)
    (Φ : LevelCaseFunction Λ j)
    (o : ∀ i, TorusSite ((L.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) (jX : L.Index),
    j + 1 ≤ S.data.windowLevel → 0 ≤ M → 0 ≤ b →
    (∀ i V, IsQuasiLocalCaseFunction ((L.points i).tower.stage j).toStepSetup (o i) Rr 0 M ∅ (fun _ => 0)
      (Φ (L.points i) V)) →
    (∀ i, Measurable (caseLift (L.points i).tower j _ (Φ (L.points i)))) →
    L.observables jX = caseObservable j Φ →
    (∀ i, ∀ᵐ x ∂(markedSampleLaw (L.points i).tower (L.points i).β (j + 1) ((L.points i).sideAtLevel (j + 1))),
      Disjoint (stageState (L.points i).tower (j + 1) _ x).2.1
        (supBall ((L.points i).originSite (j + 1) ((L.points i).sideAtLevel (j + 1))) (Rc : ℝ)) →
      ((markedSampleLaw (L.points i).tower (L.points i).β (j + 1) ((L.points i).sideAtLevel (j + 1)))[
        caseLift (L.points i).tower j _ (Φ (L.points i)) |
          stageSigma (L.points i).tower (j + 1) ((L.points i).sideAtLevel (j + 1))]) x ≤ b) →
    ∀ᵐ ω ∂L.law, L.condMeanAt jX ω ≤
      b + M * (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling (j + 1)))
end YangMills.Construction.MomentLaw
end
