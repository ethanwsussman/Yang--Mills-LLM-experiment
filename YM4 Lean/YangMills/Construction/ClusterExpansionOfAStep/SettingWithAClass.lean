import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
def StepSettings.ChartSetting.classExponent {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
    (s' : StepSettings.ChartSetting R n) (ch : ℝ) (θ : StepGas.GasSupport R n) : ℝ :=
  s'.densityNear θ.2 + R.coupling * R.params.κ * R.params.threshold ^ 2 *
      ((TorusLumps.hotLumpsWithin R.params (s'.field 0) θ.2).card : ℝ) +
    R.params.κ₁ * R.coupling * R.params.threshold ^ 2 *
      (TorusLumps.excessLength R.params R.range θ.2 (s'.field 0) : ℝ) -
    16 * ch * R.coupling * (TorusLumps.supportUnitCount R.params.side R.range θ : ℝ)
namespace ClusterExpansionOfAStep
def InsertClassMassBound : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (G : StepGas.GasGround R n)
      (σ : G.Config) (i : G.GasSpin) (s : StepGas.SupportState i.1), G.IsAdmissibleGround →
      G.pairConstraint.IsAdmissible σ →
      (G.settingOf (G.familyOf σ)).IsAdmissible → σ i = Sum.inl () →
      (∀ j, σ j = Sum.inl () ∨ i.1.FarApart j.1) →
      (G.settingOf ((G.familyOf σ).insertClass i.1 s)).IsAdmissible →
      (∀ b ∈ i.1.1, 1 - StepSettings.bondMark R G.coarse
        (G.frameField (StepGas.GasFamily.single i.1 s)) b ≠ 0) →
      StepGas.settingMass (G.settingOf ((G.familyOf σ).insertClass i.1 s)) ≤
        ENNReal.ofReal (Real.exp
          ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).classExponent T.gasRate i.1)) *
          StepGas.settingMass (G.settingOf (G.familyOf σ))
end ClusterExpansionOfAStep
end YangMills.Construction
end
