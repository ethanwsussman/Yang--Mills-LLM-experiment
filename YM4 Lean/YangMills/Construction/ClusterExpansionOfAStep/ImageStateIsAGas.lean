import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepGas RenormalizationStepParameters
def coarseStateGasStatement : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible →
    T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      G.groundSetting.IsAdmissible ∧ 0 < G.coldWeight ∧
      G.coldWeight = ∫ η, G.groundSetting.cutoffProduct η * Real.exp (-G.groundSetting.potential η) ∧
      coarseStateMass R G.cut G.coarse G.state =
        ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
          ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
            G.partitionFunction ∅ ∧
      coarseStateWeight R G.cut G.coarse G.state =
        R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
          (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
          G.coldWeight * G.xi ∅
end StepSettings
end YangMills.Construction
end
