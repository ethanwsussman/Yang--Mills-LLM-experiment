import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellPoincare
def cellPoincareStatement : Prop :=
  ∀ K : ℝ, 0 < K → ∃ (C c : ℝ) (L₁ : ℕ), 0 < C ∧ 0 < c ∧
    ∀ (F : BlockAverages.BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → L₁ ≤ F.blockSide →
    BlockAverages.IsAdmissibleAmbient F → 1024 ≤ m → BlockAverages.IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → BlockAverages.IsCold S F.top s V →
      ∀ ξ : F.Site 0 → ℍ[ℝ], GaugeMap.CellMeanFree S V ξ → ∀ y ∈ S,
        (∀ (Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (σ : F.Cell → ℝ),
          BlockAverages.CellNormFamily S Md Lf Sr σ K →
          Md (PatchDifferences.sectionNormOn S ξ) y ≤
            C * (GaugeMap.cellSideLength F : ℝ) *
              Md (PatchDifferences.formNormOn S
                (BlockAverages.covariantDiff (BlockAverages.referenceFieldChain S V 0) ξ)) y) ∧
        BlockAverages.weightedLpNormOnCell 12 S (fun _ => 1) (PatchDifferences.sectionNormOn S ξ) y ≤
          C * BlockAverages.weightedLpNormOnCell 3 S (fun _ => 1)
            (PatchDifferences.formNormOn S
              (BlockAverages.covariantDiff (BlockAverages.referenceFieldChain S V 0) ξ)) y
end YangMills.Construction.CellPoincare
end
