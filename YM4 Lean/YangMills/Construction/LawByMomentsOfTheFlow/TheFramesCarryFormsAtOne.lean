import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.MeanInTheColdSetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion
def framesPullbackFormsStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t, t + 1 ≤ S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (Y : TorusSite n) (e : ℝ), 0 ≤ e →
    ∀ g : TorusSite (n * Λ.stepParams.side) → TorusField (n * Λ.stepParams.side) → ℝ,
    (∀ y ∈ sitesInBlocks Λ.stepParams.side {Y},
      ContDiffThreeAt (g y) (trivialField (n * Λ.stepParams.side)) ∧ HasQuadraticFormAtIdentity (g y) ∧
        IsDecayingAbout Λ.stepParams e y (hessianAtIdentity (g y))) →
    ∀ c c' : TorusBond n,
    |∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          hessianAtIdentity (fun V : TorusField n => g y (coldFieldAboveFrames (S.tower.stage t).toStepSetup V 0)) c c' -
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
          pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side
            (S.tower.stage t).depth (n := n) (hessianAtIdentity (g y)) c c'| ≤
      C 0 * S.coupling t ^ (-(1 / 2) : ℝ) * e / Λ.stepParams.weight (tripleDiam Y c c')
end YangMills.Construction.MomentLaw
end
