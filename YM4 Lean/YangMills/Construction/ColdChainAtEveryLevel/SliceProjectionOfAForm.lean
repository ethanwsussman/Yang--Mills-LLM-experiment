import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def sliceProjectionStatement : Prop :=
  ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions, ∃ v : F.Site 0 → Fin 4 → imaginaryQuaternions,
          GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) (fun x i => u x i - v x i) ∧
          ∀ (φ : F.Cell → ℝ) (δ : ℝ) (p : F.Site 0), 0 ≤ δ → δ ≤ 1 / 8 →
            (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
            weightedNorm S (referenceFieldChain S V) (baseOnlyChart v) (classWeight F φ 0 p) ≤
              C * cellwiseL4Norm S (classWeight F φ 0 p 0) (covariantDiff (referenceFieldChain S V 0)
                (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) fun x i => u x i))
end YangMills.Construction.BlockAverages
end
