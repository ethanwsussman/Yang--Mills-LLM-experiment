import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def principalHessian (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) : ℝ :=
  ∑ q ∈ plaquettesOver S S 0, inner ℝ (linearizedCurl (R 0) U.fine q) (linearizedCurl (R 0) A.fine q) +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      inner ℝ ((U.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) ((A.coarse j c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) +
    a * ∑ c ∈ bondsOver S S F.top,
      inner ℝ (linearPart R U F.top c.1 c.2) (linearPart R A F.top c.1 c.2)
def hessianNearPrincipalStatement : Prop :=
  ∀ a θ δ : ℝ, 0 < a → 0 ≤ θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
          ∀ (φ : F.Cell → ℝ) (θ' : ℝ) (p : F.Site 0), (θ' = θ ∨ θ' = 0 ∨ θ' = -θ) →
            (∀ y y', |φ y - φ y'| ≤ δ * cellSupDist y y') → ∀ U A : ChainChart F,
              |referenceSecondDeriv a S (referenceFieldChain S V) V U A - principalHessian a S (referenceFieldChain S V) U A| ≤
                C * s * weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ' p) *
                  weightedNorm S (referenceFieldChain S V) A (invertedWeights (classWeight F φ θ' p))
end YangMills.Construction.BlockAverages
end
