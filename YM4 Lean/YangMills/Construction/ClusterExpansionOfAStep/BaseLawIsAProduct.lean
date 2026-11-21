import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts
def BaseLawIsProduct : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (W : TorusField (n * R.params.side))
    (b : BaseChoice R.params.side n),
    baseLaw (R := R) W b =
      ∏ y : (stepBlockFrame R.params.side n).Cell,
        blockBaseWeight R.params (stepHotLumps R.params W) y (b y)
end YangMills.Construction.ClusterExpansionOfAStep
end
