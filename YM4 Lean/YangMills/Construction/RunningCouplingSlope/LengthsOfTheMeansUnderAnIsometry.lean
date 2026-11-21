import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import YangMills.Construction.SummableBoundsOfTheFlow.EnergyUnderAnIsometry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def LogContourLengthsSymmetric : Prop :=
  ∀ (F : BlockAverages.BlockFrame) (W W' : F.GaugeField F.depth) (g : BlockAverages.CubicSymmetry)
    (γ : F.Site F.depth → BlockAverages.UnitQuaternion), Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) → g.IsSymmetry F → (∀ w, γ (BlockAverages.cellCentre F.depth w) = 1) →
    EnergySymmetry.transportField g W = BlockAverages.gaugeTransform γ W' →
    ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.top,
        Real.log ‖BlockAverages.contourAverage W' c‖ =
      ∑ c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells F) F.top,
        Real.log ‖BlockAverages.contourAverage W c‖
end YangMills.Construction.SlopeCoefficient
end
