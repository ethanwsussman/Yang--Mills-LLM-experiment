import YangMills.Construction.LawInAState.HatsSumToTheFreeKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusFields WeightedResponses ResponseInTheExpansion BoxResponses ReflectionKernel
open InfiniteLattice (AmbientSpace)
open Classical in
def sitesWithinTwo {N : ℕ} [NeZero N] (S : Finset (TorusSite N)) : Finset (TorusSite N) :=
  Finset.univ.filter fun y => ∃ z ∈ S, supDist y z ≤ 2
def pairSitesStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K k : ℕ), k ≤ K → ∀ (c : AmbientSpace) (d Λ : ℝ) (f h : AmbientSpace → ℝ),
    IsLocalizedLipschitzPair c d Λ f h → 0 < d → d ≤ 1 / 100 → 64 * ((L : ℝ) ^ k / (L : ℝ) ^ K) ≤ d →
    (∀ y, y ∉ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f) →
      blockMean L k (boxSide L K k) y (unitTorusWeight L K k f) = 0) ∧
    (∀ y, y ∉ weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k h) →
      blockMean L k (boxSide L K k) y (unitTorusWeight L K k h) = 0) ∧
    ((sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f))).card : ℝ) ≤
      (15 * (d / ((L : ℝ) ^ k / (L : ℝ) ^ K))) ^ 4 ∧
    ((sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k h))).card : ℝ) ≤
      (15 * (d / ((L : ℝ) ^ k / (L : ℝ) ^ K))) ^ 4 ∧
    ∀ y ∈ sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k f)),
      ∀ z ∈ sitesWithinTwo (weightSupportSites L k (boxSide L K k) (unitTorusWeight L K k h)),
        (∀ i, |(minimalSiteDiff y z i : ℝ)| ≤ 13 * (d / ((L : ℝ) ^ k / (L : ℝ) ^ K))) ∧
        (d / ((L : ℝ) ^ k / (L : ℝ) ^ K)) ^ 2 / 4 ≤ normSq fun i => (minimalSiteDiff y z i : ℝ)
end YangMills.Construction.StateLaws
end
