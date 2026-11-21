import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def gaugeMapDifferenceNearCellStatement : Prop :=
  ∃ (c C : ℝ) (L₀ : ℕ), 0 < c ∧ 0 < C ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell),
    Odd F.blockSide → L₀ ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z₀ : F.Cell), z₀ ∈ S →
        Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z₀} 0, ‖covariantDiff (referenceFieldChain S V 0)
            (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun x i => u x i) b.1 b.2‖ ^ 4)) ≤
          C * ∑ z ∈ cellBall S z₀ 22, localNorm S (referenceFieldChain S V) (baseOnlyChart u) (constOneWeights F) z
end YangMills.Construction.BlockAverages
end
