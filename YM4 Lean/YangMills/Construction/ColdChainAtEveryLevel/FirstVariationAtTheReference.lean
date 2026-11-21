import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def referenceFirstVariationStatement : Prop :=
  ∀ a θ δ : ℝ, 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → ∃ (Ca : ℝ) (L₀ : ℕ), 0 < Ca ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ∃ l0 : ChainChart F → ℝ,
            (∀ A A', l0 (chartSum A A') = l0 A + l0 A') ∧
            (∀ (t : ℝ) A, l0 (chartMove (zeroChart F) A t) = t * l0 A) ∧
            ∀ (A : ChainChart F) (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
              |l0 A| ≤ Ca * s * weightedNorm S (referenceFieldChain S V) A
                (invertedWeights (decayWeights F δ θ' p y0)) ∧
              |deriv (fun τ : ℝ => chartAction a S (referenceFieldChain S V)
                  (chartMove (zeroChart F) A τ) V) 0 - l0 A| ≤
                C * s ^ 2 * weightedNorm S (referenceFieldChain S V) A
                  (invertedWeights (decayWeights F δ θ' p y0))
end YangMills.Construction.BlockAverages
end
