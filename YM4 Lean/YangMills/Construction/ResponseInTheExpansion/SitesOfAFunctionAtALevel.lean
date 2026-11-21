import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def levelSitesStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (t n : ℕ) [NeZero n],
    (∀ (f g : FreeEnergies.FinePlaquetteFunction) (W : ℝ),
      (∀ p p' : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L t n),
        f (LevelTestFunctions.barycenterCoord p.1) ≠ 0 →
        g (LevelTestFunctions.barycenterCoord p'.1) ≠ 0 →
        W ≤ FreeEnergies.MomentSetup.fineDist (WeightedResponses.fineSide L t n) (LevelTestFunctions.barycenterCoord p.1)
          (LevelTestFunctions.barycenterCoord p'.1)) →
      ∀ a ∈ weightSupportSites L t n (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t n)),
      ∀ a' ∈ weightSupportSites L t n (FreeEnergies.fineWeight g (WeightedResponses.fineSide L t n)),
        W ≤ 2 * ((L : ℝ) ^ t * TorusFields.supDist a a' + (L : ℝ) ^ t)) ∧
    (∀ (f : FreeEnergies.FinePlaquetteFunction) (R : ℝ),
      (∀ p p' : WeightedResponses.OrientedPlaquette (WeightedResponses.fineSide L t n),
        f (LevelTestFunctions.barycenterCoord p.1) ≠ 0 →
        f (LevelTestFunctions.barycenterCoord p'.1) ≠ 0 → ∀ q,
        |LevelTestFunctions.circleRep (WeightedResponses.fineSide L t n) (LevelTestFunctions.barycenterCoord p.1 q -
          LevelTestFunctions.barycenterCoord p'.1 q)| ≤ R) →
      ∀ a ∈ weightSupportSites L t n (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t n)),
      ∀ a' ∈ weightSupportSites L t n (FreeEnergies.fineWeight f (WeightedResponses.fineSide L t n)),
        (L : ℝ) ^ t * TorusFields.supDist a a' ≤ R + (L : ℝ) ^ t) ∧
    ∀ (A : Finset (TorusFields.TorusSite n)) (R : ℕ), (∀ a ∈ A, ∀ a' ∈ A, TorusFields.supDist a a' ≤ R) →
      A.card ≤ (2 * R + 1) ^ 4
end YangMills.Construction.ResponseInTheExpansion
end
