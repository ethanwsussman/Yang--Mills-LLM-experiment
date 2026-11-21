import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.GaugeMap
variable {F : BlockFrame}
def weightedSliceEstimateStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ δ Cₐ : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < Cₐ ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ∀ (φ : F.Cell → ℝ) (p : F.Site 0) (θ' : ℝ), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
            (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
            ∀ (U : ChainChart F) (f : ChainChart F → ℝ) (B : ℝ), 0 ≤ B →
              InGaugeSlice S V (referenceFieldChain S V 0) U.fine →
              (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
                referenceSecondDeriv a S (referenceFieldChain S V) V U A = f A) →
              (∀ A : ChainChart F, InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
                |f A| ≤ B * weightedNorm S (referenceFieldChain S V) A
                  (invertedWeights (classWeight F φ θ' p))) →
              weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) ≤ Cₐ * B
end YangMills.Construction.BlockAverages
end
