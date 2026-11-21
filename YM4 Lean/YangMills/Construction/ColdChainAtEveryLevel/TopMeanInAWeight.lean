import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def topAverageInDecayWeightStatement : Prop :=
  ∀ del : ℝ, 0 < del → del ≤ 1 / 8 → ∃ K : ℝ, 0 < K ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (A : ChainChart F) (θ' : ℝ) (p : F.Site 0) (y0 : F.Cell), 0 ≤ θ' → θ' ≤ 1 / 8 →
          ∀ b ∈ innerBonds S F.top,
            ‖linearPart (referenceFieldChain S V) A F.top b.1 b.2‖ ≤
              K * weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0)) ∧
            ∀ q : ℍ[ℝ], HasDerivAt
                (fun τ : ℝ => gaugedBondAverage (referenceFieldChain S V) (chartMove (zeroChart F) A τ) F.depth b) q 0 →
              ‖q * (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - linearPart (referenceFieldChain S V) A F.top b.1 b.2‖ ≤
                C * s * weightedNorm S (referenceFieldChain S V) A (invertedWeights (decayWeights F del θ' p y0))
end YangMills.Construction.BlockAverages
end
