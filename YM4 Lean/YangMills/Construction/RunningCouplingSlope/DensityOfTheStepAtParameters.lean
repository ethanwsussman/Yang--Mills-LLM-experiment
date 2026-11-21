import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters ReferenceDensity
namespace RunningCouplingSlope
def withSideAndThreshold (ℓ : StepParameters) (m : ℕ) (s : ℝ) : StepParameters :=
  { ℓ with n₀ := m, threshold := s }
def paramStepDensity (T : ParameterAssignment) (t : ℕ) : LocalDensity :=
  stepDensityFamily T.coupling T.ρA T.lam T.side t
structure HasStepDensityBounds (s : ℝ) (ℓ : StepParameters) (c C : ℝ) (h : LocalDensity) : Prop where
  admissible : IsAdmissibleDensity (withSideAndThreshold ℓ 64 s) h
  analyticAt : ∀ n [NeZero n], 64 ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold s W →
    ∀ (k : ℕ) (e : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => h n y (perturb e X τ W)) 0
  decay : DerivDecay (withSideAndThreshold ℓ 64 s) h fun _ m => C * Real.exp (-(c * m))
  decay_wider : DerivDecay (withSideAndThreshold ℓ 64 (9 / 8 * s)) h fun _ m => C * Real.exp (-(c * m))
  local_comparison : LocalComparison (withSideAndThreshold ℓ 64 s) h fun m => C * Real.exp (-(c * m))
def StepDensityBoundsAtFixedParameters : Prop :=
  ∃ (rt₀ cD : ChainParameters → ℝ), (∀ l, 0 < rt₀ l) ∧ (∀ l, 0 < cD l) ∧
    ∀ T : ParameterAssignment, T.Admissible → ∃ C : ℝ, 0 < C ∧
      (∀ (y : ℝ) (t : ℕ), T.floorMin ≤ y →
        HasStepDensityBounds T.threshold (T.stepParameters y) (cD T.toChainParameters) C (paramStepDensity T t)) ∧
      (T.rt ≤ rt₀ T.toChainParameters → 4 * (T.rt / 2 ^ 10) ≤ cD T.toChainParameters ∧ ∃ Ch : ℝ, 0 < Ch ∧
        ∀ (y : ℝ) (t : ℕ), T.floorMin ≤ y → IsCurvatureFamily (T.stepParameters y) Ch (paramStepDensity T t))
end RunningCouplingSlope
end YangMills.Construction
end
