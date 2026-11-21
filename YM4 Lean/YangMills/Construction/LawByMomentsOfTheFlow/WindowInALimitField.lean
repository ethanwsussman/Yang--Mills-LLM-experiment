import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
variable {Λ : MomentParameters}
namespace MomentPoint
variable (S : MomentPoint Λ)
open Classical in
def goodCaseForms (u d n : ℕ) [NeZero n] (B : Finset (Fin Λ.k)) :
    WeightedResponses.CaseFunction (S.tower.stage u).toStepSetup n :=
  fun W Yt _ _ _ => if S.IsGoodConfig u (n * Λ.stepParams.side) W Yt then
    S.formProductMean d (n * Λ.stepParams.side) B (S.cutoffColourForm u (n * Λ.stepParams.side) W) else 0
end MomentPoint
def levelObservable (u : ℕ)
    (f : (S : MomentPoint Λ) → WeightedResponses.StageState S.tower u (S.sideAtLevel u) → ℝ) :
    SampleObservable Λ := fun S w =>
  if hu : u ≤ S.data.windowLevel then f S (S.stateAtLevel u hu w) else 0
open Classical in
def notGoodIndicator (u : ℕ) : SampleObservable Λ :=
  levelObservable u fun S q => if S.IsGoodConfig u (S.sideAtLevel u) q.1 q.2.1 then 0 else 1
open Classical in
def goodCurvaturePower (u power : ℕ) : SampleObservable Λ :=
  levelObservable u fun S q => if S.IsGoodConfig u (S.sideAtLevel u) q.1 q.2.1 then
    (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature u (S.sideAtLevel u) q.1) ^ power else 0
open Classical in
def badResponseProduct (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  if S.IsGoodConfig S.lastSeparated (S.sideAtLevel S.lastSeparated)
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).1
      (S.stateAtLevel S.lastSeparated S.lastSeparated_le w).2.1 then 0
  else ∏ i ∈ B, |S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i
    (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)|
def meanScoreProduct (J : List (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  (J.map fun i => S.meanScore S.lastSeparated (S.sideAtLevel S.lastSeparated) i
    (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)).prod
end YangMills.Construction.MomentLaw
end
