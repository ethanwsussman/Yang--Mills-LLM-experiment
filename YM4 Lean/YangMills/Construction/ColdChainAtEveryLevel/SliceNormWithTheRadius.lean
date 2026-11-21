import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def sliceNormRadiusBoundStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ (c Ca : ℝ) (L1 : ℕ), 0 < c ∧ 0 < Ca ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell),
    Odd F.blockSide → L1 ≤ F.blockSide → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
    ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ (φ : F.Cell → ℝ) (θ δ : ℝ) (p : F.Site 0), |θ| ≤ 1 / 8 → |δ| ≤ 1 / 8 →
        (∀ y y', |φ y - φ y'| ≤ |δ| * cellSupDist y y') →
        ∀ U : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
          weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ p) +
            weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
              (fun x i => U.fine x i) ≤
            Ca * Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) U (classWeight F φ θ p))
end YangMills.Construction.BlockAverages
end
