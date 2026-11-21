import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames TorusFields
def FamilyAtMinimizerAnalytic : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ (t : ℕ) (f : TorusLumps.LocalDensity),
    (∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ => f n y (perturb c X τ W)) 0) →
    ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        AnalyticAt ℝ (fun τ : Fin k → ℝ => familyAtMinimizer T.a T.ρA T.L t f n y (perturb c X τ W)) 0
end YangMills.Construction.ReferenceDensity
end
