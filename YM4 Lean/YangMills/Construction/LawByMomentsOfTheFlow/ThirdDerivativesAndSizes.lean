import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses BlockAverages
def thirdDerivativeBoundsStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
    (∀ W : TorusField n, IsCold Λ.stepParams.threshold W →
      ContDiffThreeAt (fun W' => (S.resp t).cold n y W' h) W ∧
      ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
        |mixedDeriv (fun W' => (S.resp t).cold n y W' h) W c X| ≤
          C 0 * weightNorm Λ.stepParams.side (S.tower.stage t).depth h /
            Λ.stepParams.weight (supportDiam y c)) ∧
    ∀ b b' : TorusBond n, |classicalQuadratic S.tower S.resp t n h y b b'| ≤
      C 1 * weightNorm Λ.stepParams.side (S.tower.stage t).depth h / Λ.stepParams.weight (tripleDiam y b b')
end YangMills.Construction.MomentLaw
end
