import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def transportedCurlBoundStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 → ∃ (C c : ℝ) (L₁ : ℕ), 0 < C ∧ 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → L₁ ≤ F.blockSide →
      IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (p : F.Site 0) (A B : ℝ), 0 ≤ A → 0 ≤ B →
          ∑ q ∈ innerPlaquettes (BlockWeights.cellsNearPoint S p) 0,
            (BlockWeights.shiftedWeight F θ p 0 q.1 *
              ‖PlaquetteExpansion.covariantCurlAt (referenceFieldChain S V 0) f q‖) ^ 2 ≤ A ^ 2 →
          ∑ b ∈ innerBonds (BlockWeights.cellsNearPoint S p) 0,
            (BlockWeights.shiftedWeight F θ p 0 b.1 * ‖f b.1 b.2‖) ^ 4 ≤ B ^ 4 →
          ∀ q ∈ innerPlaquettes (BlockWeights.cellsNearPoint S p) F.depth,
            ‖PlaquetteExpansion.covariantCurlAt (referenceFieldChain S V F.depth)
                (transportedForm (referenceFieldChain S V) f F.depth) q‖ ≤
              (BlockWeights.shiftedWeight F θ p F.depth q.1)⁻¹ * (2 * A) + C * s * B
end YangMills.Construction.BlockAverages
end
