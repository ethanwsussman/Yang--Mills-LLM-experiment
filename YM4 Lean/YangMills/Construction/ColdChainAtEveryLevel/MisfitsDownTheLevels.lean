import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def misfitDecayDownLevelsStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V W : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (U : ChainChart F) (β : ℝ), s ≤ β → β ≤ c →
          (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ β) →
          (∀ b ∈ innerBonds S F.top,
            normSubOne (chartBondMisfit (referenceFieldChain S V) U W F.depth b) ≤ β) →
          (∀ A : ChainChart F, IsStationaryAlong a S (referenceFieldChain S V) W U A) →
          ∀ (j : ℕ) (z : F.Cell), j < F.top →
            cellMisfitSum S (referenceFieldChain S V) U W j 4 z ≤
                (C * β * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
            cellMisfitSum S (referenceFieldChain S V) U W j 2 z ≤
                (C * β * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2
end BlockAverages
end YangMills.Construction
end
