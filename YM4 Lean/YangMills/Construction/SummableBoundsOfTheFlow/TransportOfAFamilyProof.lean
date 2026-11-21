import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfAFamilyProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Interpolation.TransportOfFamily
theorem eventuallyInParameters_mono {P Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : ∀ T, 1 ≤ T.E → 0 < T.η₃ → P T → Q T)
    (hP : EventuallyInParameters P) : EventuallyInParameters Q := by apply _root_.YangMills.Construction.Interpolation.FlatLimitOfFamily.eventuallyInParameters_mono <;> assumption
theorem transportAtEveryScale_of_scaling (hS : transportScalingStatement)
    (hT : expansionTransportStatement) : TransportAtEveryScale :=
  eventuallyInParameters_mono (fun T hE hη hA => hS T (by linarith) hη hA) hT
end Interpolation.TransportOfFamily
end YangMills.Construction
end
