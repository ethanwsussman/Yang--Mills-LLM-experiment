import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ScaledVariables
def ObservableMeanSlopeVanishes : Prop :=
  ForallSmoothObservables fun T _ _ _ f law _ _ V Ob k c X =>
    k ≤ 3 → Filter.Tendsto
      (deriv fun l => ColdStepAtMirrorFrames.bondDeriv
        (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
      (𝓝[>] 0) (𝓝 0)
end YangMills.Construction.ScaledVariables
end
