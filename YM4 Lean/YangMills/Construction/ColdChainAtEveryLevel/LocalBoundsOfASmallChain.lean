import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def smallChartLocalBoundsStatement : Prop :=
  ∀ θ δ : ℝ, 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (β : ℝ), s ≤ β → β ≤ c →
          (∀ (p : F.Site 0) (y0 : F.Cell),
            weightedNorm S (referenceFieldChain S V) U (decayWeights F δ θ p y0) ≤ β) →
          (∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
            localQuarticSum S (referenceFieldChain S V) U j p r ≤
              (C * β) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ)) ∧
          ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ F.top →
            localCurvatureSum S (referenceFieldChain S V) U p r ≤ (C * β) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) ∧
            localMisfitSum S (referenceFieldChain S V) U V p r ≤ (C * β) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ)
end BlockAverages
end YangMills.Construction
end
