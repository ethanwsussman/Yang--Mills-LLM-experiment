import YangMills.Construction.SummableBoundsOfTheFlow.EnergyUnderAnIsometry
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity EnergySymmetry
def stepAmplitudeSymmetryStatement : Prop :=
  ∀ (F : BlockFrame) (a ρ : ℝ) (V V' : F.GaugeField F.top) (g : CubicSymmetry) (γ : F.Site F.depth → UnitQuaternion),
    Odd F.blockSide →
    (∀ i, 2 ≤ F.extent i) → g.IsSymmetry F → 0 < ρ → ρ ≤ 1 → g.TransportsField V V' →
    IsMinimizingChart a (finiteCells F) V ρ (coordsAboveFrame true a ρ 0 V 0) →
    IsMinimizingChart a (finiteCells F) V' ρ (coordsAboveFrame true a ρ 0 V' 0) →
    (∀ z, γ (cellCentre F.depth z) = 1) →
    transportField g (fieldAboveFrame true a ρ 0 V 0) = gaugeTransform γ (fieldAboveFrame true a ρ 0 V' 0) →
    (chartedHessian a ρ V 0).PosDef → (chartedHessian a ρ V' 0).PosDef →
    -(1 / 2) * Real.log (chartedHessian a ρ V' 0).det +
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame true a ρ 0 V' 0 b.1.1 b.1.2) =
      -(1 / 2) * Real.log (chartedHessian a ρ V 0).det +
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2)
end YangMills.Construction.RunningCouplingSlope
end
