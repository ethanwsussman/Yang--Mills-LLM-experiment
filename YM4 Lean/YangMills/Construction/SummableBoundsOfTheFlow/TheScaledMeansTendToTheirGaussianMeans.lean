import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
def scaledMeansTendToGaussianMeans : Prop :=
  ForallSmoothObservables fun T _ _ _ f law _ _ V Ob k c X =>
    k ≤ 3 → Filter.Tendsto
      (fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
      (𝓝[>] 0) (𝓝 (bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X))
end ScaledVariables
end YangMills.Construction
end
