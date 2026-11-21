import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames StepSettings StepGas
def AllowedStatesMeasurable : Prop :=
  ∀ (R : StepSetup), R.params.Admissible → R.HasExpansions → IsCutoff R.ballRadius R.barrierFn →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n) (i : G.GasSpin), G.IsAdmissibleGround →
    MeasurableSet {s : SupportState i.1 | G.IsAllowed i.1 s}
end YangMills.Construction.ClusterExpansionOfAStep
end
