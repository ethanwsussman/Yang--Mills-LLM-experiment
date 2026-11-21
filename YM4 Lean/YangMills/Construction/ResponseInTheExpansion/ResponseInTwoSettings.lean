import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open StepSettings TorusFields TorusLumps StepGas BlockAverages RenormalizationStepParameters
def ChartResponseComparison : Prop :=
  HoldsAtEveryStep fun _ S P =>
    (∀ (n : ℕ) [NeZero n] (c : ChartSetting S n), S.params.n₀ ≤ n → c.IsAdmissible → ∀ (y : TorusSite (n * S.params.side))
      (w : PlaquetteWeight (fineSide S.params.side S.depth (n * S.params.side))),
      |chartResponse P c y w| ≤ (P.responseParams.C₀ + chartSiteScore P c y) * weightNorm S.params.side S.depth w) ∧
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (c : ChartSetting S n) (c' : ChartSetting S n') (Y : TorusSite n) (Y' : TorusSite n')
      (m : ℕ), S.params.n₀ ≤ n → S.params.n₀ ≤ n' → c.IsAdmissible → c'.IsAdmissible →
      (SettingsAgreeNear c c' Y Y' m → (S.range : ℝ) / (4 * S.params.side) ≤ m →
        (∀ (o : Fin 4 → ℤ), o ∈ centredCube S.params.side → ∀ (w : PlaquetteWeight (fineSide S.params.side S.depth (n * S.params.side)))
          (w' : PlaquetteWeight (fineSide S.params.side S.depth (n' * S.params.side))),
          WeightsAgreeAt S.params.side S.depth (fineSite S.params.side Y 0 o) (fineSite S.params.side Y' 0 o) w w' →
          |chartResponse P c (fineSite S.params.side Y 0 o) w - chartResponse P c' (fineSite S.params.side Y' 0 o) w'| ≤
            (1 + chartSiteScore P c (fineSite S.params.side Y 0 o)) * Real.exp (-(S.params.rt * m / 2 ^ 5)) * weightNorm S.params.side S.depth w) ∧
        ∀ b : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin b →
          |chartBondScore c (bondFrom Y b) - chartBondScore c' (bondFrom Y' b)| ≤
            Real.exp (-(S.params.rt * m / 2 ^ 5))) ∧
      (SettingsAgreeAwayFromFrames c c' Y Y' m → 16 * S.frameReach ≤ m →
        (∀ (o : Fin 4 → ℤ), o ∈ centredCube S.params.side → ∀ (w : PlaquetteWeight (fineSide S.params.side S.depth (n * S.params.side)))
          (w' : PlaquetteWeight (fineSide S.params.side S.depth (n' * S.params.side))),
          WeightsAgreeAt S.params.side S.depth (fineSite S.params.side Y 0 o) (fineSite S.params.side Y' 0 o) w w' →
          |chartResponse P c (fineSite S.params.side Y 0 o) w - chartResponse P c' (fineSite S.params.side Y' 0 o) w'| ≤
            (1 + chartSiteScore P c (fineSite S.params.side Y 0 o)) * Real.exp (-(15 / 16 * S.params.rt * m / 2 ^ 5)) *
              weightNorm S.params.side S.depth w) ∧
        ∀ b : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin b →
          |chartBondScore c (bondFrom Y b) - chartBondScore c' (bondFrom Y' b)| ≤
            Real.exp (-(15 / 16 * S.params.rt * m / 2 ^ 5)))
end WeightedResponses
end YangMills.Construction
end
