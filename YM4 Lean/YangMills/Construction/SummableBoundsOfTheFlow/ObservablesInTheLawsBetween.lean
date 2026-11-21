import YangMills.Construction.SummableBoundsOfTheFlow.MomentsInTheLawsBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def observableSizesStatement : Prop :=
  ∃ Cq : StepParameters → ℕ → ℝ,
    EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
      (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E
        T.energyRatio T.L t T.n₀ (frameRadius x) d) →
      ∀ M₀ : LawOnBondVariables ι,
        M₀.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
          T.L t T.n₀ (frameRadius x) d →
        ObservableSizes T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.decayRate
          T.η₃ T.L t T.n₀ (frameRadius x) T.σ T.p (Cq (momentParameters T))
          (convexCombinationExponent T.chainParams.lam x w M) M₀
end Interpolation
end YangMills.Construction
end
