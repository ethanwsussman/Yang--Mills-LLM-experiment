import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def torusWeightAtBarycentres (L K m : ℕ) (f : InfiniteLattice.AmbientSpace → ℝ) :
    WeightedResponses.PlaquetteWeight m := fun p =>
  BoxResponses.periodizeUnitTorus f fun i =>
    ((WeightedResponses.doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)
def markWeightsOnUnitTorusStatement : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K : ℕ) (d vt : ℝ), 0 < d → d ≤ 1 / 4 → 0 < vt →
    ∀ (p : ℕ) (φ : Fin p → InfiniteLattice.AmbientSpace → ℝ), IsSeparatedBumpFamily d vt φ →
    ∀ (t n : ℕ) [NeZero n], t ≤ K → n = 2 * L ^ (K - t) →
      (∀ i, WeightedResponses.weightSup
        (torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ i)) ≤ 1) ∧
      (∀ i, WeightedResponses.weightLipschitz L t
        (torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ i)) ≤
          2 / (vt * (d * (L : ℝ) ^ (K - t)))) ∧
      (∀ i, ((ResponseInTheExpansion.weightSupportSites L t n
        (torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ i))).card : ℝ) ≤
          (2 * (d * (L : ℝ) ^ (K - t)) + 2) ^ 4) ∧
      (∀ i j, i ≠ j → ∀ y ∈ ResponseInTheExpansion.weightSupportSites L t n
          (torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ i)),
        ∀ y' ∈ ResponseInTheExpansion.weightSupportSites L t n
          (torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ j)),
          d / 2 * (L : ℝ) ^ (K - t) ≤ (TorusFields.supDist y y' : ℝ) + 1) ∧
      ∀ i, torusWeightAtBarycentres L K (WeightedResponses.fineSide L t n) (φ i) =
        FreeEnergies.fineWeight
          (fun b => BoxResponses.periodizeUnitTorus (φ i) fun a => b a / (L : ℝ) ^ K)
          (WeightedResponses.fineSide L t n)
end YangMills.Construction.StateLaws
end
