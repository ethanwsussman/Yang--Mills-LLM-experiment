import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def coldTopCriticalChainStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ θ del Ca : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 0 < del ∧ del ≤ 1 / 8 ∧ 0 < Ca ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ rL sL CL : ℝ, 0 < rL ∧ 0 < sL ∧ 0 < CL ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
        IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ sL → IsCold S F.top s V →
          ∃ U : ChainChart F,
            GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U.fine ∧
            supWeightedNorm S del (referenceFieldChain S V) U ≤ rL ∧
            (∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) V U A) ∧
            (∀ U' : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) U'.fine →
              supWeightedNorm S del (referenceFieldChain S V) U' ≤ rL →
              (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
                IsStationaryAlong a S (referenceFieldChain S V) V U' A) → ChartEqOnBonds S U U') ∧
            (∃ Ulin Urest : ChainChart F, ChartEqOnBonds S U (chartSum Ulin Urest) ∧
              ∀ (p : F.Site 0) (y0 : F.Cell) (θ' : ℝ), θ' = θ ∨ θ' = 0 →
                weightedNorm S (referenceFieldChain S V) Ulin (decayWeights F del θ' p y0) ≤ Ca * s ∧
                weightedNorm S (referenceFieldChain S V) Urest (decayWeights F del θ' p y0) ≤ CL * s ^ 2) ∧
            (∀ A : ChainChart F, GaugeMap.InGaugeSlice S V (referenceFieldChain S V 0) A.fine →
              (1 / 4) * quadraticFormNormSq a S (referenceFieldChain S V) A (oneSiteWeights F) ≤
                deriv (deriv fun τ : ℝ => chartAction a S (referenceFieldChain S V) (chartMove U A τ) V) 0) ∧
            IsCold S F.depth (s / 8) (chartField (referenceFieldChain S V) U F.depth) ∧
            (∀ (j : ℕ) (p : F.Site 0) (r : ℝ), j < F.top → 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ (F.top - j) →
              localQuarticSum S (referenceFieldChain S V) U j p r ≤
                (CL * s) ^ 4 * (r / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ)) ∧
            (∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ F.top →
              localCurvatureSum S (referenceFieldChain S V) U p r ≤
                  (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) ∧
              localMisfitSum S (referenceFieldChain S V) U V p r ≤
                  (CL * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ)) ∧
            ∀ (j : ℕ) (z : F.Cell), j < F.top →
              cellMisfitSum S (referenceFieldChain S V) U V j 4 z ≤
                  (CL * s * (4 / (L : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
              cellMisfitSum S (referenceFieldChain S V) U V j 2 z ≤
                  (CL * s * (4 / (L : ℝ)) ^ (F.top - 1 - j)) ^ 2
end YangMills.Construction.BlockAverages
end
