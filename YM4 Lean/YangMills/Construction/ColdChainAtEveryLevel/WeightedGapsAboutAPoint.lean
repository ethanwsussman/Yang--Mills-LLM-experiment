import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.WeightsUpTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open BlockWeights
def weightedLevelGapsStatement : Prop :=
  ∀ θ δ : ℝ, 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (p : F.Site 0) (β : ℝ), 0 ≤ β → β ≤ c →
          (∀ y₀ : F.Cell, weightedNorm S (referenceFieldChain S V) U (decayWeights F δ θ p y₀) ≤ β) →
          ∀ j, j < F.top → ∑ b ∈ innerBonds (cellsNearPoint S p) j,
            (shiftedWeight F θ p j b.1 * ‖levelCoordinate (referenceFieldChain S V) U j b.1 b.2‖) ^ 4 ≤ (C * β) ^ 4
end BlockAverages
end YangMills.Construction
end
