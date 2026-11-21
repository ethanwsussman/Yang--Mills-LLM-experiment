import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.LogarithmsOfTheCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def topMeanVelocityStatement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
          (∀ b ∈ innerBonds S F.top,
              ‖gaugedBondAverage (referenceFieldChain S V) U F.depth b * (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
                C * (s + supWeightedNorm S δ (referenceFieldChain S V) U)) ∧
          ∀ A : ChainChart F,
            ∑ b ∈ innerBonds S F.top,
                ‖deriv (fun τ : ℝ => gaugedBondAverage (referenceFieldChain S V) (chartMove U A τ) F.depth b) 0 *
                    (((V b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
                  linearPart (referenceFieldChain S V) A F.top b.1 b.2‖ ^ 2 ≤
              (C * (s + supWeightedNorm S δ (referenceFieldChain S V) U)) ^ 2 *
                weightedNorm S (referenceFieldChain S V) A (oneSiteWeights F) ^ 2
end BlockAverages
end YangMills.Construction
end
