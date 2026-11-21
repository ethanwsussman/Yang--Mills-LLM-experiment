import YangMills.Construction.Torus.CoversAndLocalisationData
import YangMills.Construction.Weighted.InverseExpansionConstants
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def LocalAveragedSquareInverse : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty →
    expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
    ∀ (ι : Type) (P : ι → D.CoverPiece) (c : ℝ), B.IsCover c P →
      ∀ (δ : B.Localization P) (i : ι),
        (∀ w : B.LayerFn,
          (∀ y : ↥B.allSites, (y : D.Space) ∉ B.pieceSites (P i) → w y = 0) →
          lowerBoundConst 4 * B.layerSpaceNorm ((B.scaleOnLayer ^ 2) w) ^ 2 ≤
            B.layerInner w
              (B.extendByZeroFromBlocks (δ.region i) (δ.localAvgGreenSq i) w)) ∧
        ∃ R : Module.End ℝ B.LayerFn,
          B.pieceIndicatorOp (P i) * R * B.pieceIndicatorOp (P i) = R ∧
          (B.pieceIndicatorOp (P i) *
              (B.extendByZeroFromBlocks (δ.region i) (δ.localAvgGreenSq i) :
                Module.End ℝ B.LayerFn) *
              B.pieceIndicatorOp (P i)) * R = B.pieceIndicatorOp (P i) ∧
          R * (B.pieceIndicatorOp (P i) *
              (B.extendByZeroFromBlocks (δ.region i) (δ.localAvgGreenSq i) :
                Module.End ℝ B.LayerFn) *
              B.pieceIndicatorOp (P i)) = B.pieceIndicatorOp (P i) ∧
          ∀ y y' : ↥B.allSites,
            |B.kernel R y y'| ≤
              2 / lowerBoundConst 4 * B.siteScale y ^ (-4 : ℤ) *
                Real.exp (-(2 * expansionDecayRate 4 D.L) * B.weightedDistance y y')
end YangMills.Construction.Weighted
