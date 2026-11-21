import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields
namespace TorusLumps
def stepDensityAnalyticStatement : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n →
    ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => T.stepDensity t n y (perturb c X τ W)) 0
end TorusLumps
end YangMills.Construction
end
