import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchDifferences
def covariantDiffPatchRemainderStatement : Prop :=
  ∀ K : ℝ, 0 < K → ∃ (C c : ℝ) (L₁ : ℕ), 0 < C ∧ 0 < c ∧
    ∀ (F : BlockAverages.BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide → L₁ ≤ F.blockSide →
    BlockAverages.IsAdmissibleAmbient F → 1024 ≤ m → BlockAverages.IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → BlockAverages.IsCold S F.top s V →
      ∀ ξ : F.Site 0 → ℍ[ℝ], GaugeMap.CellMeanFree S V ξ → ∀ z ∈ S,
        ∃ (e : LatticeFractionalIntegration.Lattice4 → ℍ[ℝ]) (δ : F.Site 0 → ℝ),
        PatchRemainder S V z ξ e δ C ∧
        ∀ (Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (σ : F.Cell → ℝ),
          BlockAverages.CellNormFamily S Md Lf Sr σ K →
          ∑ y ∈ BlockAverages.cellBall S z 20, Md δ y ≤ C * s * ∑ y ∈ BlockAverages.cellBall S z 20,
            (Md (BlockAverages.restrictToPatch S z (sectionNormOn S ξ)) y / (GaugeMap.cellSideLength F : ℝ) +
              Md (BlockAverages.restrictToPatch S z
                (formNormOn S (BlockAverages.covariantDiff (BlockAverages.referenceFieldChain S V 0) ξ))) y)
end YangMills.Construction.PatchDifferences
end
