import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfThePoint
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
variable {Λ : MomentParameters}
open Classical in
def clampBasesToBlocks {L n : ℕ} (b : StepCosts.BaseChoice L n) : StepCosts.BaseChoice L n := fun c =>
  if b c ∈ LumpContours.sitesBelow 0 c then b c else BlockAverages.cellCentre 0 c
theorem clampBasesToBlocks_of_isBaseChoice {L n J₀ : ℕ}
    {lumps : Finset (Finset ((TorusLumps.stepBlockFrame L n).Site 0))} {b : StepCosts.BaseChoice L n}
    (hb : LumpContours.IsBaseChoice J₀ lumps b) : clampBasesToBlocks b = b := by
  classical
  funext c
  unfold clampBasesToBlocks
  split_ifs with hin
  · rfl
  · by_cases hcase : LumpContours.nearbyLumps lumps c = ∅ ∨ LumpContours.IsCrowded J₀ lumps c
    · exact ((hb c).1 hcase).symm
    · exact absurd ((hb c).2 hcase).1 hin
namespace MomentPoint
variable (S : MomentPoint Λ)
def variableCaseProduct (u : ℕ) (J : Finset (Fin Λ.k)) (V : TorusFields.TorusField (S.sideAtLevel (u + 1))) :
    WeightedResponses.CaseFunction (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1)) :=
  fun W Yt ωt bad b => ∏ i ∈ J,
    FreeEnergies.liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse (S.resp u) V (S.weight i _))
      W Yt ωt bad (clampBasesToBlocks b)
def stepErrorBound (C : ℝ) (u : ℕ) (J : Finset (Fin Λ.k)) : ℝ :=
  C * (∑ i ∈ J, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) *
    Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 7)) *
    ∏ i ∈ J, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)))
def supportRadius (u : ℕ) : ℕ := ⌈Λ.R * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - u)⌉₊ + 2
end MomentPoint
def responseAtLevel (u : ℕ) (i : Fin Λ.k) : SampleObservable Λ := fun S w =>
  if hu : u ≤ S.data.windowLevel then S.supportTotal u (S.sideAtLevel u) i (S.stateAtLevel u hu w) else 0
def meanScoreAtLevel (u : ℕ) (i : Fin Λ.k) : SampleObservable Λ := fun S w =>
  if hu : u ≤ S.data.windowLevel then S.meanScore u (S.sideAtLevel u) i (S.stateAtLevel u hu w) else 0
def centredStepScore (u : ℕ) (i : Fin Λ.k) : SampleObservable Λ := fun S w =>
  if hu : u + 1 ≤ S.data.windowLevel then
    WeightedResponses.sourceTerm S.tower S.coeff u (S.sideAtLevel (u + 1)) (S.weight i _)
        (S.sampleAtLevel (u + 1) hu w) -
      ResponseInTheExpansion.stepMeanShift (n := S.sideAtLevel (u + 1)) (S.resp u) (S.weight i _)
  else 0
def variableProduct (u : ℕ) (J : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  if hu : u + 1 ≤ S.data.windowLevel then
    FreeEnergies.caseLift S.tower u _ (S.variableCaseProduct u J) (S.sampleAtLevel (u + 1) hu w)
  else 0
def variableMean (u : ℕ) (J : Finset (Fin Λ.k)) : SampleObservable Λ := fun S w =>
  if hu : u + 1 ≤ S.data.windowLevel then
    FreeEnergies.caseMeanAtSample S.tower u _ (S.variableCaseProduct u J) (S.sampleAtLevel (u + 1) hu w)
  else 0
def offsetCube (ρ : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(ρ : ℤ)) (ρ : ℤ)
end YangMills.Construction.MomentLaw
end
