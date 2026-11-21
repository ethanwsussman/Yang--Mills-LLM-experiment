import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion TwoLevelMixtures
def frameFieldResponseAtIdentityStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t, t + 1 ≤ S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∃ Z : TorusBond (n * Λ.stepParams.side) → TorusBond n → ℝ,
      (∀ g : TorusField (n * Λ.stepParams.side) → ℝ, ContDiffThreeAt g (trivialField (n * Λ.stepParams.side)) →
        HasQuadraticFormAtIdentity g → ∀ c c' : TorusBond n,
        hessianAtIdentity (fun V : TorusField n => g (coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' =
          ∑ b : TorusBond (n * Λ.stepParams.side), ∑ b' : TorusBond (n * Λ.stepParams.side),
            Z b c * hessianAtIdentity g b b' * Z b' c') ∧
      (∀ (b : TorusBond (n * Λ.stepParams.side)) (c : TorusBond n),
        |Z b c - responseKernel Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side
            (S.tower.stage t).depth b c| ≤
          C 0 * S.coupling t ^ (-(1 / 2) : ℝ) *
            Real.exp (-(2 * Λ.stepParams.weightRate * bondSiteDist Λ.stepParams.side b c.1))) ∧
      ∀ (b : TorusBond (n * Λ.stepParams.side)) (c : TorusBond n),
        |responseKernel Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side
            (S.tower.stage t).depth b c| ≤
          C 1 * Real.exp (-(2 * Λ.stepParams.weightRate * bondSiteDist Λ.stepParams.side b c.1))
end YangMills.Construction.MomentLaw
end
