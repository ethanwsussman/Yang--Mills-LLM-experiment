import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShareFamilies
open BlockAverages ColdStepAtMirrorFrames TorusFields
structure ShareBounds (T : ColdStepAtMirrorFrames.StepParameters) (ℓ : TorusLumps.StepParameters) (t : ℕ) : Prop where
  family : TorusLumps.IsCurvatureFamily ℓ
    (TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ * TorusLumps.maxOfFirstFour T.chainParams.N) (levelShareFamily T.a T.L (t + 1))
  invariant : TorusLumps.SumInvariantUnderIsometries ℓ (levelShareFamily T.a T.L (t + 1))
  form : TorusLumps.HasCurvatureForm (levelShareFamily T.a T.L (t + 1)) 1
  analytic : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => levelShareFamily T.a T.L (t + 1) n y (perturb c X τ W)) 0
  higherDeriv_le : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 4 ≤ k → k ≤ 6 → AreUnitVectors X →
      |mixedDeriv (levelShareFamily T.a T.L (t + 1) n y) W c X| ≤
        TorusLumps.weightGrowthSup ℓ.rt ℓ.n₁ * T.chainParams.N k / ℓ.weight (supportDiam y c)
def SharesBoundedAlongParameters : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ t, ShareBounds T ℓ t
end YangMills.Construction.ShareFamilies
end
