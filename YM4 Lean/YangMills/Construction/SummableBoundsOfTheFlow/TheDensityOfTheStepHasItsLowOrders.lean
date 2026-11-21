import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace TorusLumps
def stepDensityLowOrderStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ →
    ℓ.Admissible → ∀ t,
    IsAdmissibleDensity ℓ (T.stepDensity t) ∧
    DerivDecay ℓ (T.stepDensity t) (fun _ m => T.Cs * Real.exp (-(T.κ / 2 ^ 6 * m))) ∧
    LocalComparison ℓ (T.stepDensity t) fun m => T.Cs * Real.exp (-(T.κ / 2 ^ 9 * m))
end TorusLumps
end YangMills.Construction
end
