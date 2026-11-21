import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfTheScaledMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def scaledMeanSecondDerivTendsToCoeff : Prop :=
  ForallSmoothObservables fun T _ _ _ f law _ _ V Ob k c X =>
    k ≤ 2 → Filter.Tendsto
      (iteratedDeriv 2 fun l => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X)
      (𝓝[>] 0) (𝓝 (2 * bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X))
end YangMills.Construction.ScaledVariables
end
