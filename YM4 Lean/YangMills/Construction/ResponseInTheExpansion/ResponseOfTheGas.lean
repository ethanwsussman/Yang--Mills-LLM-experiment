import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open StepSettings TorusFields TorusLumps StepGas BlockAverages RenormalizationStepParameters
def GasResponseBounds : Prop :=
  HoldsAtEveryStep fun T S P =>
    (∀ (n : ℕ) [NeZero n] (G : GasGround S n), G.IsAdmissibleGround →
      (∀ (y : TorusSite (n * S.params.side)) (w : PlaquetteWeight (fineSide S.params.side S.depth (n * S.params.side))),
        |gasResponseShift P G y w| ≤
          (1 + recordedSiteScore P G y) * Real.exp (-(6 * T.gasRate * S.coupling)) * weightNorm S.params.side S.depth w ∧
        |G.expectation ∅ fun σ => chartResponse P (configSetting G σ) y w| ≤
          (P.responseParams.C₀ + recordedSiteScore P G y + Real.exp (-(6 * T.gasRate * S.coupling))) * weightNorm S.params.side S.depth w) ∧
      ∀ b : TorusBond n, |gasBondScoreShift G b| ≤ Real.exp (-(6 * T.gasRate * S.coupling)) ∧
        |G.expectation ∅ fun σ => chartBondScore (configSetting G σ) b| ≤ 2 + Real.exp (-(6 * T.gasRate * S.coupling))) ∧
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround S n) (G' : GasGround S n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → GroundsAgreeNear G G' Y Y' m → 16 * S.frameReach ≤ m →
      (∀ (o : Fin 4 → ℤ), o ∈ centredCube S.params.side → ∀ (w : PlaquetteWeight (fineSide S.params.side S.depth (n * S.params.side)))
        (w' : PlaquetteWeight (fineSide S.params.side S.depth (n' * S.params.side))),
        WeightsAgreeAt S.params.side S.depth (fineSite S.params.side Y 0 o) (fineSite S.params.side Y' 0 o) w w' →
        |gasResponseShift P G (fineSite S.params.side Y 0 o) w - gasResponseShift P G' (fineSite S.params.side Y' 0 o) w'| ≤
          (1 + recordedSiteScore P G (fineSite S.params.side Y 0 o)) *
            Real.exp (-(2 * T.gasRate * S.coupling) - S.params.rt * m / 2 ^ 8) * weightNorm S.params.side S.depth w) ∧
      ∀ b : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin b →
        |gasBondScoreShift G (bondFrom Y b) - gasBondScoreShift G' (bondFrom Y' b)| ≤
          Real.exp (-(2 * T.gasRate * S.coupling) - S.params.rt * m / 2 ^ 8)
end YangMills.Construction.WeightedResponses
end
