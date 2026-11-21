import YangMills.Construction.ColdChainAtEveryLevel.ComparedCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.TheShareIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def agreeingPairsShareComparisonStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (c : ℝ) (r₀ : ℕ) (C : ℕ → ℝ), 0 < c ∧ (∀ k, 0 ≤ C k) ∧
    ∀ (F F' : BlockFrame) (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell), F.blockSide = L → F'.blockSide = L →
      F'.depth = F.depth →
      IsAdmissibleAmbient F → IsAdmissibleAmbient F' → 1024 ≤ m → IsOrthantRegular S m → IsOrthantRegular S' m →
      ∀ (s : ℝ) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 0 < s →
        s ≤ c → IsCold S F.top s V → IsCold S' F'.top s V' → r₀ ≤ r → AgreeOnBall S V S' V' Y Y' r →
        ∀ (U : ChainChart F) (U' : ChainChart F'),
          (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ c) →
          (∀ z ∈ S', localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') z ≤ c) →
          AreComparedRepresentations S (referenceFieldChain S V) Y Y' (topBondsMeetingCell S Y) C U U'
              (localCellShare a S (referenceFieldChain S V) V Y)
              (localCellShare a S' (referenceFieldChain S' V') V' Y') ∧
          |localCellShare a S (referenceFieldChain S V) V Y U (fun _ _ => 0) -
              localCellShare a S' (referenceFieldChain S' V') V' Y' U' fun _ _ => 0| ≤
            C 0 * (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
              localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y') *
              offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' U U' ∧
          ∀ (n : ℕ) (A : Fin n → ChainChart F) (A' : Fin n → ChainChart F')
            (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions)
            (e' : Fin n → F'.Site F'.top → Fin 4 → imaginaryQuaternions), n = 1 →
            (∀ l, ∀ b ∈ topBondsMeetingCell S Y, e l b.1 b.2 = e' l (cellAtSameOffset Y Y' b.1) b.2) →
            ‖localIteratedDeriv (localCellShare a S (referenceFieldChain S V) V Y) U A e -
                localIteratedDeriv (localCellShare a S' (referenceFieldChain S' V') V' Y') U' A' e'‖ ≤
              C 1 * (offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' U U' *
                  ∏ l, localDirectionSize S (referenceFieldChain S V) (topBondsMeetingCell S Y) Y (A l) (e l) +
                (s + localNorm S (referenceFieldChain S V) U (oneSiteWeights F) Y +
                  localNorm S' (referenceFieldChain S' V') U' (oneSiteWeights F') Y') *
                  ∑ l, offsetChartGapNorm S (referenceFieldChain S V) Y Y Y' (A l) (A' l))
end YangMills.Construction.BlockAverages
end
