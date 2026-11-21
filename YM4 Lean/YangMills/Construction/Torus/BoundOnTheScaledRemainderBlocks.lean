import YangMills.Construction.Torus.CoversAndLocalisationData
import YangMills.Construction.Weighted.InverseExpansionConstants
import YangMills.Construction.Weighted.LayerOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
namespace SeparatedChain.Localization
variable {D : TorusData} {B : SeparatedChain D} {ι : Type*} {𝒟 : ι → D.CoverPiece}
  (δ : B.Localization 𝒟)
def localScaledExt (i : ι) : Module.End ℝ B.LayerFn :=
  B.extendByZeroFromBlocks (δ.region i) (δ.localScaledGreenSq i)
def cutScaled (i : ι) : Module.End ℝ B.LayerFn :=
  B.pieceIndicatorOp (𝒟 i) * δ.localScaledExt i * B.pieceIndicatorOp (𝒟 i)
open Classical in
def remainderBlock (i' i : ι) : Module.End ℝ B.LayerFn :=
  if i' = i then
    (B.pieceCutoffOp (𝒟 i) * δ.cutScaled i -
        δ.cutScaled i * B.pieceCutoffOp (𝒟 i)) +
      B.pieceIndicatorOp (𝒟 i) * (δ.localScaledExt i - B.scaledGreenSq) *
        B.pieceCutoffOp (𝒟 i)
  else
    (B.pieceIndicatorOp (𝒟 i) - 1) * B.pieceCutoffOp (𝒟 i') ^ 2 *
        B.scaledGreenSq * B.pieceCutoffOp (𝒟 i)
end SeparatedChain.Localization
def ScaledRemainderBoundStatement : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D), (B.stage 0).Nonempty →
    6 * (D.L : ℝ) ≤ (D.blockNumber : ℝ) →
    expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
    ∀ (ι : Type) (𝒟 : ι → D.CoverPiece) (c : ℝ), B.IsCover c 𝒟 →
      ∀ (δ : B.Localization 𝒟) (i : ι) (y y'' : ↥B.allSites),
        (y'' : D.Space) ∈ B.pieceSites (𝒟 i) →
        ∑ᶠ i', |B.matrixOf (δ.remainderBlock i' i) y y''| ≤
          expansionConstFirst 4 D.L c * (D.blockNumber : ℝ)⁻¹ *
            Real.exp (-(1 / 16 * greenDecayRate 4 D.L) * B.weightedDistance y y'')
end YangMills.Construction.Weighted
end
