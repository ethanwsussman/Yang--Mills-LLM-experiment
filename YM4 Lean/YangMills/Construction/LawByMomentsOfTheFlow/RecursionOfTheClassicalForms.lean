import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses TorusLumps
def classicalQuadraticRecursionStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S =>
    (∀ t, t < S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
      ∀ (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
        (Y : TorusSite n) (c c' : TorusBond n),
      classicalQuadratic S.tower S.resp (t + 1) n h Y c c' =
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side
            (S.tower.stage t).depth (classicalQuadratic S.tower S.resp t (n * Λ.stepParams.side) h y) c c' +
        Λ.stepParams.coupling / 2 *
          blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h * ∑ i : Fin 4,
          (fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
              (S.tower.stage t).depth (Y, i) c *
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
              (S.tower.stage t).depth (Y, i) c' +
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
              (S.tower.stage t).depth (Y - unitStep n i, i) c *
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
              (S.tower.stage t).depth (Y - unitStep n i, i) c')) ∧
    ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (h : PlaquetteWeight n)
      (h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage 0).depth n)), HEq h h' →
      ∀ A : TorusBond n → ℝ, ∑ y : TorusSite n, bilinearEval (classicalQuadratic S.tower S.resp 0 n h' y) A A =
        ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), h p * curl A p ^ 2
end YangMills.Construction.MomentLaw
end
