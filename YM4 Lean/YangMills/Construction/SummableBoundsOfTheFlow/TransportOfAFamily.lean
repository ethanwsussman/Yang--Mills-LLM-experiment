import YangMills.Construction.SummableBoundsOfTheFlow.TransportScalesWithTheFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace Interpolation
def TransportAtEveryScale : Prop := EventuallyInParameters fun T => ∀ ε : ℝ, 0 < ε → TransportAtScale T ε
end Interpolation
end YangMills.Construction
end
