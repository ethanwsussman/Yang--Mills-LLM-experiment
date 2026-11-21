import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormsOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def stepGradientsDecoupledStatement : Prop :=
  ForAllPoints fun Λ C c _ S => ∀ s : ℕ, s = S.data.windowLevel →
    ∀ μ : Measure (LevelChain Λ.stepParams.side s (S.data.period Λ.stepParams.side)),
    IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling s (S.data.period Λ.stepParams.side)) μ →
    ∀ (j : ℕ) (hj : j + 1 ≤ s), s - j - 1 < S.lastSeparated →
      ∃ w : Fin Λ.k → Fin 3 × ChartBondIndex Λ.stepParams.side (s - j - 1)
          (WeightedResponses.fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) → ℝ,
        (∀ i b, 0 < w i b) ∧
        (∀ i b, Integrable (fun X => |S.levelStepGradient (s - j - 1)
            (WeightedResponses.fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i
            (CompletedForms.levelPair j s (S.data.period Λ.stepParams.side) hj X).1
            (CompletedForms.levelPair j s (S.data.period Λ.stepParams.side) hj X).2 b| ^ Λ.k) μ ∧
          ∫ X, |S.levelStepGradient (s - j - 1)
            (WeightedResponses.fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) i
            (CompletedForms.levelPair j s (S.data.period Λ.stepParams.side) hj X).1
            (CompletedForms.levelPair j s (S.data.period Λ.stepParams.side) hj X).2 b| ^ Λ.k ∂μ ≤ w i b ^ Λ.k) ∧
        ∀ i i', i ≠ i' → ∑ b, ∑ b', w i b *
            |fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 (s - j - 1)
              (WeightedResponses.fineSide Λ.stepParams.side j (S.data.period Λ.stepParams.side)) b b'| * w i' b' ≤
          C 0 * (Λ.stepParams.side : ℝ) ^ (8 * (S.data.scaleLevel - (s - j - 1))) *
            Real.exp (-(c * (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - (s - j - 1))))
end YangMills.Construction.MomentLaw
end
