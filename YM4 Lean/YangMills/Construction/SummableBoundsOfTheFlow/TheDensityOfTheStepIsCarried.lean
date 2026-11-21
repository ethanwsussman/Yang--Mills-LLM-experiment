import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames
def StepDensitySumInvariant : Prop :=
  EventuallyOrdered fun T => ∀ P : TorusLumps.StepParameters, T.Compatible P → P.Admissible →
    ∀ t, TorusLumps.SumInvariantUnderIsometries P (T.stepDensity t)
end YangMills.Construction.ReferenceDensity
end
