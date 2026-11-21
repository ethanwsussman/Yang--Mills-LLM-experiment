import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts
structure StepSettings.ChartSetting.HasFullDecay {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n)
    (u : FreeCoords s.free → ℝ) (lam C : ℝ) : Prop extends s.HasDecay u lam C where
  contDiffOn_nhds : ∃ U : Set (FreeCoords s.free), IsOpen U ∧ (∀ η, s.InBalls η → η ∈ U) ∧ ContDiffOn ℝ 3 u U
  mixedSecondDeriv_le : ∀ η, s.InBalls η → ∀ b b' X X', ‖X‖ = 1 → ‖X'‖ = 1 →
    |mixedSecondDeriv u η b b' X X'| ≤ C * R.coupling
def StepSettings.ChartSetting.gaussianMixPotential {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n)
    (lam τ : ℝ) (η : FreeCoords s.free) : ℝ :=
  τ * s.partPotential 0 η + (1 - τ) * (R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2)
open Classical in
def StepSettings.ChartSetting.cutGaussianMixPotential {R : StepSetup} {n : ℕ} [NeZero n] (s : ChartSetting R n)
    (lam τ : ℝ) (X : Finset s.free) (η : FreeCoords s.free) : ℝ :=
  τ * (s.partPotential 0 (s.restrictTo X η) + R.coupling * lam / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2) +
    (1 - τ) * (R.coupling * lam / 2 * ∑ b, ‖η b‖ ^ 2)
def ClusterExpansionOfAStep.SettingsUniformlyConvex : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 < C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n →
        ∀ s : ChartSetting R n, s.IsAdmissible →
          s.HasFullDecay s.potential T.lam C ∧
          (∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 → s.HasFullDecay (s.partPotential ν) T.lam C) ∧
          (∀ (v : ℝ) (X : Finset s.free), 0 ≤ v → v ≤ 1 →
            s.HasFullDecay (s.interpolatedPotential T.lam v X) T.lam C) ∧
          (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → s.HasFullDecay (s.gaussianMixPotential T.lam τ) T.lam C) ∧
          ∀ (τ : ℝ) (X : Finset s.free), 0 ≤ τ → τ ≤ 1 →
            s.HasFullDecay (s.cutGaussianMixPotential T.lam τ X) T.lam C
end YangMills.Construction
end
