import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitField
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusLumps TorusFields WeightedResponses ResponseInTheExpansion HullTrees StepSettings
variable {Λ : MomentParameters}
open Classical in
def badOrSupportSiteCase (j : ℕ)
    (Z : (S : MomentPoint Λ) → Finset (TorusSite (S.sideAtLevel (j + 1) * Λ.stepParams.side))) :
    LevelCaseFunction Λ j :=
  fun S _ _ Yt _ bad _ => if ((bad.image Prod.fst ∪ Yt) ∩ Z S).Nonempty then 1 else 0
def siteIndicatorLimitBoundStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (j Rc Rr : ℕ)
    (Z : (S : MomentPoint Λ) → Finset (TorusSite (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (m Nz E : ℝ)
    (o : ∀ i, TorusSite ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) (jX : F.Index),
    j + 1 ≤ S.data.windowLevel → 0 ≤ m → 0 ≤ E → 0 ≤ Nz →
    (S.tower.stage j).nextCoupling ≤ 1.01 * (S.tower.stage j).coupling →
    (∀ i, ((Z (F.points i)).card : ℝ) ≤ Nz) →
    (∀ i, ∀ y ∈ Z (F.points i), supBall (parentBlock Λ.stepParams.side y) m ⊆
      supBall ((F.points i).originSite (j + 1) ((F.points i).sideAtLevel (j + 1))) (Rc : ℝ)) →
    (∀ i (c : TorusSite ((F.points i).sideAtLevel (j + 1))),
      ((blocksNearFreeCores Λ.stepParams.side ((F.points i).tower.stage j).toStepSetup.range
        (supBall c m)).card : ℝ) *
        Real.exp (-(7 * Λ.table.gasRate * ((F.points i).tower.stage j).coupling)) ≤ E) →
    (∀ i, ∀ y ∈ Z (F.points i), y ∈ supBall (o i) (Rr : ℝ) ∧
      ∀ μ : Fin 4, y + unitStep _ μ ∈ supBall (o i) (Rr : ℝ)) →
    F.observables jX = caseObservable j (badOrSupportSiteCase j Z) →
    ∀ᵐ v ∂F.law, F.condMeanAt jX v ≤
      Nz * E + (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling (j + 1)))
end YangMills.Construction.MomentLaw
end
