import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation
namespace StepDensities
def oneLoopCoeffBound : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ t : ℕ, TorusLumps.HasCurvatureForm (T.stepDensity t) (T.oneLoopCoeff t) ∧
      |T.oneLoopCoeff t| ≤ TorusLumps.baseConstant T.Cs T.κ
end StepDensities
end YangMills.Construction
end
