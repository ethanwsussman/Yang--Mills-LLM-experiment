import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def scaledMeansSmoothInScale : Prop :=
  ForallSmoothObservables fun T _ _ l₁ f law _ _ V Ob k c X =>
    k ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ → ContDiffAt ℝ (if k = 3 then 2 else 3)
      (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l
end YangMills.Construction.ScaledVariables
end
