import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def scaledMeansBounded : Prop :=
  ForallSmoothObservables fun T C K l₁ f law _ Y V Ob k c X =>
    ∀ (i : ℕ) (l : ℝ), IsControlledOrder k i → 0 < l → l ≤ l₁ →
      |iteratedDeriv i (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l| ≤
        C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
end YangMills.Construction.ScaledVariables
end
