import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergies
open StepSettings StepGas StepCosts TorusFields WeightedResponses
def settingMeanMeasurableStatement : Prop :=
  HoldsAtEveryStep fun _ R _ => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ F : CaseFunction R n,
    (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b) →
    open Classical in Measurable fun σ : G.Config =>
      if G.pairConstraint.IsAdmissible σ then settingMean (configSetting G σ) (G.badBondsOf σ) F else 0
end FreeEnergies
end YangMills.Construction
end
