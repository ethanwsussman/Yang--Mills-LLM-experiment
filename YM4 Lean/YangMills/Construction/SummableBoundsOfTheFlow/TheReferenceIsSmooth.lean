import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms TorusFields TorusLumps ReferenceDensity
namespace StepDensities
structure ReferenceBoundsAtLevel (T : ColdStepAtMirrorFrames.StepParameters) (ℓ : TorusLumps.StepParameters)
    (Eh : ℕ → ℝ) (t : ℕ) : Prop where
  family : IsNormBoundedFamily ℓ (T.E / 2) (T.energyRatio / 2) (T.referenceDensity t)
  vanishing_curvatureForm : HasVanishingCurvatureForm (T.referenceDensity t)
  analytic : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => T.referenceDensity t n y (perturb c X τ W)) 0
  isometries : SumInvariantUnderIsometries ℓ (T.referenceDensity t)
  higherDeriv_le : ∀ n [NeZero n], T.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold T.σ W →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 4 ≤ k → k ≤ 6 → AreUnitVectors X →
      |mixedDeriv (T.referenceDensity t n y) W c X| ≤ Eh k / ℓ.weight (supportDiam y c)
structure ReferenceFullBoundsAtLevel (T : ColdStepAtMirrorFrames.StepParameters) (ℓ : TorusLumps.StepParameters)
    (Eh : ℕ → ℝ) (t : ℕ) : Prop
    extends ReferenceBoundsAtLevel T ℓ Eh t where
  curvatureForm_minimizer : HasCurvatureForm (familyAtMinimizer T.a T.ρA T.L t (T.referenceDensity t)) 0
  curvatureForm_step : HasCurvatureForm (T.stepDensity t) (T.oneLoopCoeff t)
  oneLoopCoeff_abs_le : |T.oneLoopCoeff t| ≤ baseConstant T.Cs T.κ
def referenceSmoothStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ Eh : ℕ → ℝ,
    ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible → ∀ t,
    ReferenceFullBoundsAtLevel T ℓ Eh t
end StepDensities
end YangMills.Construction
end
