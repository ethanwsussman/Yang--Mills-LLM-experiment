import YangMills.Construction.CellOfTheFlow.TheStepGivenItsStateIsTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def supportsPresentRarelyStatement : Prop :=
  WeightedResponses.HoldsAtAdmissibleParameters fun Tb y =>
    ∀ R : StepSettings.StepSetup, R.OnParameters Tb y → R.nextCoupling ≤ 1.01 * R.coupling →
      ∀ (m : ℕ) [NeZero m] (G : StepGas.GasGround R m)
        (Θ : Finset (TorusLumps.ClusterSupport R.params.side m)), G.IsAdmissibleGround →
        G.gibbsLaw ∅ (supportsPresent G Θ) ≤
          ENNReal.ofReal (∏ θ ∈ Θ, TorusLumps.clusterWeight R.params.side Tb.gasRate R.coupling R.range θ)
end YangMills.Construction.CellWindows
end
