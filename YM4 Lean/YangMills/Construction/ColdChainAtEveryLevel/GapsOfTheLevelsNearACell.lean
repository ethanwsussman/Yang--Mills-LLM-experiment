import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import YangMills.Construction.ColdChainAtEveryLevel.CoordinatesAtTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def levelGapNearCellStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (ρ : ℝ) (V : F.GaugeField F.top), 0 < ρ → ρ ≤ c → IsCold S F.top ρ V →
        ∀ (W : ChainChart F) (x : F.Cell) (β : ℝ), x ∈ S → 0 ≤ β → β ≤ c →
          localNorm S (referenceFieldChain S V) W (oneSiteWeights F) x ≤ β →
          ∀ k, k < F.top →
            ∑ e ∈ innerBonds (cellBall S x 1) k,
              normSubOne (chartGap (referenceFieldChain S V) W k e.1 e.2) ^ 4 ≤ (C * β) ^ 4 ∧
            ∑ e ∈ bondsOver S {x} k,
              normSubOne (chartGap (referenceFieldChain S V) W k e.1 e.2) ^ 4 ≤ (C * β) ^ 4
end YangMills.Construction.BlockAverages
end
