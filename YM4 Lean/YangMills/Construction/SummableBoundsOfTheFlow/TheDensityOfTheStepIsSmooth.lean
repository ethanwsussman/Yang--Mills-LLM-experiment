import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames TorusFields
structure StepDensityBounds (T : ColdStepAtMirrorFrames.StepParameters) (P : TorusLumps.StepParameters) (C : ℝ)
    (t : ℕ) : Prop where
  admissible : TorusLumps.IsAdmissibleDensity P (T.stepDensity t)
  decay : TorusLumps.DerivDecay P (T.stepDensity t) fun _ m => T.Cs * Real.exp (-(T.κ / 2 ^ 6 * m))
  comparison : TorusLumps.LocalComparison P (T.stepDensity t) fun m => T.Cs * Real.exp (-(T.κ / 2 ^ 9 * m))
  analytic : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => T.stepDensity t n y (perturb c X τ W)) 0
  higherDeriv_le : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 4 ≤ k → k ≤ 6 → AreUnitVectors X →
      |mixedDeriv (T.stepDensity t n y) W c X| ≤ C * Real.exp (-(2 ^ 6 * T.κ * supportDiam y c))
def StepDensityIsSmooth : Prop :=
  EventuallyOrdered fun T => ∃ C : ℝ, ∀ P : TorusLumps.StepParameters, T.Compatible P → P.Admissible →
    ∀ t, StepDensityBounds T P C t
end YangMills.Construction.ReferenceDensity
end
