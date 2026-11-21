import YangMills.Construction.SummableBoundsOfTheFlow.MomentsInTheLawsBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation
open BlockAverages ColdStepAtMirrorFrames
structure InterpolatedFrameBoundsOnTorus (T : StepParameters) {F : BlockFrame} (s x : ℝ) (m : ℕ)
    (V : F.GaugeField F.top) : Prop where
  near_minimizer : InterpolatedFrameNearMinimizer s T.a T.chainParams.ρA T.chainParams.δ₂
    (frameGapBound T m) T.σ m V
  small : InterpolatedFrameSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct T.σ m V
  slope : InterpolatedSlopeSmall s T.a T.chainParams.ρA T.chainParams.δ₂ T.Ct (frameGapBound T m) x m V
  exponent : InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs m V
  variation : TopVariationRepresentation s T.a T.chainParams.ρA T.ballRadius T.κ T.Cs m V
structure InterpolatedFrameBoundsAt (T : StepParameters) (Cq Cz : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ)
    (t : ℕ) (x : ℝ) : Prop where
  one_torus : ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedFrameBoundsOnTorus T s x (frameRadius x) V
  two_tori : ∀ (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell) (r : ℕ) (s : ℝ), IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → 0 ≤ s → s ≤ 1 →
    InterpolatedFrameLocal s T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.K T.Ct T.σ
        (frameRadius x) V V' Y Y' r ∧
      InterpolatedSlopeLocal s T.a T.chainParams.ρA T.κ T.Ct x (frameRadius x) V V' Y Y' r
  laws : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (n : ℕ) (w : Fin n → ℝ)
    (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E
      T.energyRatio T.L t T.n₀ (frameRadius x) d) →
    HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d
        (convexCombinationExponent T.chainParams.lam x w M) ∧
      LawMomentBounds T.ballRadius x T.κ T.Cs T.p Cq Cr d
        (convexCombinationExponent T.chainParams.lam x w M) ∧
      ∀ M₀ : LawOnBondVariables ι,
        M₀.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
          T.L t T.n₀ (frameRadius x) d →
        ObservableSizes T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.decayRate
          T.η₃ T.L t T.n₀ (frameRadius x) T.σ T.p Cz
          (convexCombinationExponent T.chainParams.lam x w M) M₀
def interpolatedFramesStatement : Prop :=
  ∃ (Cq Cz : StepParameters → ℕ → ℝ) (Cr : StepParameters → ℕ → ℕ → ℕ → ℝ),
    EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      InterpolatedFrameBoundsAt T (Cq (momentParameters T)) (Cz (momentParameters T))
        (Cr (momentParameters T)) t x
end Interpolation
end YangMills.Construction
end
