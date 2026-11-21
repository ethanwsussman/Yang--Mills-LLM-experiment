import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusLumps StepSettings RenormalizationStepParameters Dobrushin
namespace StepGas
def ClusterIntegralLeWeight : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (n : ℕ) [NeZero n] (G : GasGround R n) (σ : G.Config) (i : G.GasSpin), G.IsAdmissibleGround →
      G.pairConstraint.IsAdmissible σ →
      (G.settingOf (G.familyOf σ)).IsAdmissible → σ i = Sum.inl () →
      (∀ j, σ j = Sum.inl () ∨ i.1.FarApart j.1) →
      ∫⁻ v, ENNReal.ofReal (G.weight (Function.update σ i (Sum.inr v))) ∂(G.spinStateMeasure i) ≤
        ENNReal.ofReal (clusterWeight R.params.side T.gasRate R.coupling R.range i.1) *
          ENNReal.ofReal (G.weight σ)
end StepGas
end YangMills.Construction
end
