import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepPolarity
def bondIndicator {n : ℕ} (c : TorusFields.TorusBond n) : TorusFields.TorusBond n → ℝ := by
  classical exact fun c' => if c' = c then 1 else 0
def polarIdentityStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyOrdered fun T => ∀ [NeZero T.L],
    (∀ (u m : ℕ) [NeZero m] (b b' : TorusFields.TorusBond m), 64 ≤ m →
      WeightedResponses.maxwellKernel T.a T.L u b b' = WeightedResponses.maxwellKernel T.a T.L u b' b) ∧
    ∀ (u n : ℕ) [NeZero n] (c : TorusFields.TorusBond n) (φ : TorusFields.TorusBond (n * T.L) → ℝ)
      (B : TorusFields.TorusBond n → ℝ), 64 ≤ n →
      WeightedResponses.maxwellForm T.a T.L u (fun b => WeightedResponses.responseKernel T.a T.ρA T.L u b c) φ +
        T.a * ∑ c' : TorusFields.TorusBond n,
          (TwoLevelMixtures.contourMean T.L (fun b => WeightedResponses.responseKernel T.a T.ρA T.L u b c) c' -
            bondIndicator c c') *
          (TwoLevelMixtures.contourMean T.L φ c' - B c') =
      WeightedResponses.maxwellForm T.a T.L (u + 1) (bondIndicator c) B
end YangMills.Construction.StepPolarity
end
