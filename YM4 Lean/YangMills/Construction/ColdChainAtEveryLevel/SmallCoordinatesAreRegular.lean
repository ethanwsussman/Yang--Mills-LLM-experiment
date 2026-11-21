import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def smallChartIsRegularStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
          ChartIsRegular S (referenceFieldChain S V) U ∧
          ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤
            2 * supWeightedNorm S δ (referenceFieldChain S V) U
end BlockAverages
end YangMills.Construction
end
