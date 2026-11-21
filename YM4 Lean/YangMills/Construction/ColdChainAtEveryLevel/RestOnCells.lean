import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapOnDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def gaugeRemainderCellBoundStatement : Prop :=
  ∀ K : ℝ, 0 < K → ∃ (C c : ℝ) (L₁ : ℕ), 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → L₁ ≤ F.blockSide →
    IsAdmissibleAmbient F → 1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      (∀ u : F.Site 0 → Fin 4 → ℍ[ℝ], GaugeMap.CellMeanFree S V (GaugeMap.gaugeMap S V (referenceFieldChain S V 0) u)) ∧
      ∀ ξ : F.Site 0 → ℍ[ℝ], GaugeMap.CellMeanFree S V ξ →
        GaugeMap.CellMeanFree S V (gaugeRemainder S V ξ) ∧
        ∀ (Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (σ : F.Cell → ℝ), CellNormFamily S Md Lf Sr σ K → ∀ z₀ ∈ S,
          Md (PatchDifferences.formNormOn S (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ))) z₀ ≤
            C * s * ∑ y ∈ cellBall S z₀ 22, (Md (PatchDifferences.sectionNormOn S ξ) y / (GaugeMap.cellSideLength F : ℝ) +
              Md (PatchDifferences.formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)) y)
end YangMills.Construction.BlockAverages
end
