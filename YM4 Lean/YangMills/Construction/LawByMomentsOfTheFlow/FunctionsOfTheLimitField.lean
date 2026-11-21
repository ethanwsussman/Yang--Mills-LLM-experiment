import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings WeightedResponses ResponseInTheExpansion BlockAverages HullTrees
variable {Λ : MomentParameters}
def bottomProduct (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  ∏ i ∈ B, (curvatureObservable (S.weight i _) (bottomField Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) w) - c i)
def completedProduct (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  ∏ i ∈ B, (WeightedResponses.completedObservable S.tower S.coeff S.lastSeparated (S.sideAtLevel S.lastSeparated) (S.weight i _)
    (S.sampleAtLevel S.lastSeparated S.lastSeparated_le w) - c i)
def responseProduct (B : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  ∏ i ∈ B, S.supportTotal S.lastSeparated (S.sideAtLevel S.lastSeparated) i (S.stateAtLevel S.lastSeparated S.lastSeparated_le w)
namespace MomentPoint
variable (S : MomentPoint Λ)
def kappaAtLast (i : Fin Λ.k) : ℝ := S.kappa S.lastSeparated (S.sideAtLevel S.lastSeparated) i
def siteAt (u : ℕ) (z : Fin 4 → ℤ) : TorusSite (S.sideAtLevel u) := S.originSite u (S.sideAtLevel u) + siteOfInt z
end MomentPoint
open Classical in
def largeHullIndicator (u : ℕ) (z : Fin 4 → ℤ) (D : ℝ) : SampleObservable Λ := fun S w =>
  if h : u ≤ S.data.windowLevel then
    if S.siteAt u z ∈ (S.stateAtLevel u h w).2.1 ∧
      D ≤ (supDiam (hullClass (stageRange S.tower u) (S.stateAtLevel u h w).2.1 (S.siteAt u z)) : ℝ) then 1 else 0
  else 0
def hullSizePower (u : ℕ) (z : Fin 4 → ℤ) (k : ℕ) : SampleObservable Λ := fun S w =>
  if h : u ≤ S.data.windowLevel then
    siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.sampleAtLevel u h w) (S.siteAt u z) ^ k
  else 0
end YangMills.Construction.MomentLaw
end
