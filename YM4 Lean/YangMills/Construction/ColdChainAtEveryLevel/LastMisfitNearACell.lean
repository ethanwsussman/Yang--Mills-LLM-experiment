import YangMills.Construction.ColdChainAtEveryLevel.ChainCoordinatesMovedAndCriticalFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def topMisfitNearCellStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
      ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ c → IsCold S F.top r V →
        ∀ (U : ChainChart F) (z : F.Cell) (β : ℝ), z ∈ S → 0 ≤ β → β ≤ c →
          localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ β →
          ∀ b ∈ bondsOver S {z} F.top,
            normSubOne (chartBondMisfit (referenceFieldChain S V) U V F.depth b) ≤ C * (r + β)
end BlockAverages
end YangMills.Construction
end
