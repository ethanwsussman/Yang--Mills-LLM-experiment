import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def mixturesOfIntermediateLawsConvex : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x) d) →
    HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d (convexCombinationExponent T.chainParams.lam x w M)
end Interpolation
end YangMills.Construction
end
