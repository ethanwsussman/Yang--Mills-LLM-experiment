import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def observableMeanContDiffThreeStatement : Prop :=
  ForallSmoothObservables fun T _ _ l₁ f law _ _ V Ob _ _ _ =>
    ∀ l : ℝ, 0 < l → l ≤ l₁ → ContDiffThreeAlongBonds (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V
end YangMills.Construction.ScaledVariables
end
