import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames TorusFields
def StepDensityHigherDerivBound : Prop :=
  EventuallyOrdered fun T => ∃ C : ℝ, ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n →
    ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      4 ≤ k → k ≤ 6 → AreUnitVectors X →
      |mixedDeriv (T.stepDensity t n y) W c X| ≤ C * Real.exp (-(2 ^ 6 * T.κ * supportDiam y c))
end YangMills.Construction.StepDensities
end
