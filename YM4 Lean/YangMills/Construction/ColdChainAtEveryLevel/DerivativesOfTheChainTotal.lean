import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def chartActionDerivativeBoundsStatement : Prop :=
  ∃ L0 : ℕ, ∀ (L : ℕ) (a θ δ : ℝ), Odd L → L0 ≤ L → 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 →
    ∃ (c C : ℝ) (Ck : ℕ → ℝ),
    0 < c ∧ 0 < C ∧ (∀ k, 0 < Ck k) ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ U : ChainChart F, supWeightedNorm S δ (referenceFieldChain S V) U ≤ c →
          (∀ (k : ℕ) (A : Fin k → ChainChart F),
            AnalyticAt ℝ (fun t : Fin k → ℝ =>
              chartAction a S (referenceFieldChain S V) (chartShiftMulti U A t) V) 0) ∧
          (∀ (k : ℕ), 2 ≤ k → ∀ (A : Fin k → ChainChart F) (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0)
            (l1 l2 : Fin k), l1 ≠ l2 → (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
            (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
            |iteratedFDeriv ℝ k (fun t : Fin k → ℝ =>
                chartAction a S (referenceFieldChain S V) (chartShiftMulti U A t) V) 0
              (fun l => Pi.single l 1)| ≤
              Ck k * ∑ z ∈ S, ∏ l, localNorm S (referenceFieldChain S V) (A l)
                (if l = l1 then classWeight F φ θ' p
                  else if l = l2 then invertedWeights (classWeight F φ θ' p) else constOneWeights F) z) ∧
          ∀ (A : Fin 1 → ChainChart F) (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0),
            (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) → (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') →
            |fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S (referenceFieldChain S V) (chartShiftMulti U A t) V)
                0 (Pi.single 0 1) -
              fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S (referenceFieldChain S V)
                (chartShiftMulti (zeroChart F) A t) V) 0 (Pi.single 0 1) -
              iteratedFDeriv ℝ 2 (fun t : Fin 2 → ℝ => chartAction a S (referenceFieldChain S V)
                (chartShiftMulti (zeroChart F) ![U, A 0] t) V) 0 (fun l => Pi.single l 1)| ≤
              C * supWeightedNorm S δ (referenceFieldChain S V) U *
                weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) *
                weightedNorm S (referenceFieldChain S V) (A 0) (invertedWeights (classWeight F φ θ' p))
end YangMills.Construction.BlockAverages
end
