import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def lowCostPatchBoundsStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ c : ℝ, 0 < c ∧ ∀ e0 : ℝ, 0 < e0 → e0 ≤ c →
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (X : F.FieldChain) (k : F.SiteGauge) (z : F.Cell), z ∈ S → patchAction a S z X k ≤ e0 ^ 2 →
        (∀ j, j < F.top → ∀ b ∈ patchFitBonds S z j, 1 / 2 ≤ ‖gaugedContourAverage (X j) (k (j + 1)) b‖) ∧
        ∑ j ∈ Finset.range F.top, ∑ b ∈ patchFitBonds S z j,
          ‖((bondMisfit (X j) (k (j + 1)) (X (j + 1)) b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ 4 / a * e0 ^ 2 ∧
        ∑ p ∈ patchPlaquettes S z, ‖((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ 2 * e0 ^ 2
end YangMills.Construction.BlockAverages
end
