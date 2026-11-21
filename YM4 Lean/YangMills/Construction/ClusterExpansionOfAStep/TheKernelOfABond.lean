import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.LumpContours
def updateBond {F : BlockFrame} {j : ℕ} (V : F.GaugeField j) (c : F.Site j × Fin 4) (g : UnitQuaternion) :
    F.GaugeField j :=
  Function.update V c.1 (Function.update (V c.1) c.2 g)
def BondKernelProperties : Prop :=
  (∀ s : ℝ, 0 ≤ s → 1 ≤ partitionFn s ∧ 0 ≤ logPartitionGap s) ∧
  ∀ (ℓ : StepParameters) (x : ℝ) (n : ℕ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4),
    0 < bondKernel ℓ x W V b c ∧
    Real.log (bondKernel ℓ x W V b c) =
      -(ℓ.coupling * x) * contourFit ℓ.baseDepth
          (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W V c +
        logPartitionGap (ℓ.coupling * x * ‖contourMean ℓ.baseDepth
          (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) W) b W c‖) ∧
    ∫ g : UnitQuaternion, bondKernel ℓ x W (updateBond V c g) b c ∂haarUnit = 1
end YangMills.Construction.TorusLumps
end
