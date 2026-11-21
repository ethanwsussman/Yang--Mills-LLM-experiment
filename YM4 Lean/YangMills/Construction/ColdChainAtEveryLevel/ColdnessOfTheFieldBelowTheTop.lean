import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def coldFieldBelowTopStatement : Prop :=
  ∀ θ del : ℝ, 0 < θ → θ ≤ 1 / 8 → 0 < del → del ≤ 1 / 8 → ∃ K : ℝ, 0 < K ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ∀ (U : ChainChart F) (β : ℝ), s ≤ β → β ≤ c →
            (∀ (p : F.Site 0) (y0 : F.Cell),
              weightedNorm S (referenceFieldChain S V) U (decayWeights F del θ p y0) ≤ β) →
            ∀ q ∈ innerPlaquettes S F.depth,
              plaquetteDefect (chartField (referenceFieldChain S V) U F.depth) q ≤
                K * s / (L : ℝ) ^ 2 + K * (1 / (L : ℝ)) ^ θ * β + C * β ^ 2
end YangMills.Construction.BlockAverages
end
