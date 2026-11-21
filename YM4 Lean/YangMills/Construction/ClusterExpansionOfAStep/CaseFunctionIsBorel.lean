import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepCosts StepGas StepSettings RenormalizationStepParameters TorusFields TorusLumps
def CaseIntegrandMeasurable : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      (∀ (F : CaseFunctional R n), IsCaseFunctional F → ∀ (bad : Finset (TorusBond (n * R.params.side)))
        (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n),
        Measurable fun p : TorusField (n * R.params.side) × (G.state.unlabelled Yt → R.labels.Ω) =>
          G.caseIntegrand F bad Yt b p.1 p.2) ∧
      (∀ (F : CaseFunctional R n), IsCaseFunctional F → ∀ (bad free : Finset (TorusBond (n * R.params.side)))
        (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
        (ν : G.state.unlabelled Yt → R.labels.Ω),
        Measurable (G.restIntegrand F bad Yt b free ν)) ∧
      ∀ i : G.GasSpin, MeasurableSet {s : SupportState i.1 | G.IsAllowed i.1 s} ∧
        Measurable fun v : G.SpinState i => G.activity i.1 v.1
end YangMills.Construction.ClusterExpansionOfAStep
end
