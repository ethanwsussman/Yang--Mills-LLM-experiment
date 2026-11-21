import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours
namespace TorusLumps
def KernelPlainAwayFromLumps : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (n : ℕ) [NeZero n] (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (y : (stepBlockFrame ℓ.side n).Cell) (i : Fin 4),
    nearbyLumps (fineHotLumps ℓ W) y = ∅ → nearbyLumps (fineHotLumps ℓ W) (y + unitStep 1 i) = ∅ →
    baseSitesAt ℓ.baseDepth (fineHotLumps ℓ W) y = {cellCentre 0 y} ∧
    ∀ (x : ℝ) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
      (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0),
      b ∈ baseChoices ℓ W →
      LumpContours.contourMean ℓ.baseDepth (fineHotLumps ℓ W) b W (y, i) = contourAverage W (y, i) ∧
      contourFit ℓ.baseDepth (fineHotLumps ℓ W) b W V (y, i) = blockFit W V (y, i) ∧
      bondKernel ℓ x W V b (y, i) =
        Real.exp (ℓ.coupling * x * (contourAverage W (y, i) * ((V y i)⁻¹ : UnitQuaternion)).re) /
          partitionFn (ℓ.coupling * x * ‖contourAverage W (y, i)‖)
end TorusLumps
end YangMills.Construction
end
