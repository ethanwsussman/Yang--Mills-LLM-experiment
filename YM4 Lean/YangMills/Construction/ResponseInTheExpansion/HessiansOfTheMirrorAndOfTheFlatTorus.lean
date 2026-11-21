import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps RenormalizationStepParameters
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def reflectedHessianComparisonAt : Prop :=
  ∃ C c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ)
    (o : TorusSite n) (V : TorusField n) (g : TorusSite n → BlockAverages.UnitQuaternion) (s : ℝ)
    (l l' : TorusBond (n * (Tb.stepParameters y).side) → ℝ) (e e' : Fin 3),
    IsLocalChainAbove Tb y T β k n nn x₀ → j < localChainDepth (Tb.stepParameters y) β k → 0 ≤ s →
    IsColdOnBall (Tb.stepParameters y).threshold V o (localBlockSide (Tb.stepParameters y) β k) →
    IsNearIdentity g V o
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) s →
    (∀ b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
        (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
          3 * localLogScale (Tb.stepParameters y) β k) →
      l b = 0 ∧ l' b = 0) →
    |reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth
          (localBlockSide (Tb.stepParameters y) β k) o l e ⬝ᵥ
        Matrix.mulVec (frameHessian (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).toStepSetup.frameReach
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth
            (localBlockSide (Tb.stepParameters y) β k) o
            (TorusFields.gaugeTransform (restrictGauge g (supBall o
              (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)))) V)))⁻¹
          (reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth
            (localBlockSide (Tb.stepParameters y) β k) o l' e') -
      (if e = e' then
        stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n l l' else 0)| ≤
      C * (∑ b, |l b|) * (∑ b, |l' b|) * (s + Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))) ∧
    |stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n l l'| ≤
      C * (∑ b, |l b|) * (∑ b, |l' b|) ∧
    |reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth
          (localBlockSide (Tb.stepParameters y) β k) o l e ⬝ᵥ
        Matrix.mulVec (frameHessian (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).toStepSetup.frameReach
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth
            (localBlockSide (Tb.stepParameters y) β k) o
            (TorusFields.gaugeTransform (restrictGauge g (supBall o
              (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)))) V)))⁻¹
          (reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth
            (localBlockSide (Tb.stepParameters y) β k) o l' e')| ≤
      C * (∑ b, |l b|) * (∑ b, |l' b|)
def reflectedHessianComparisonStatement : Prop := HoldsOnParameterFamilies reflectedHessianComparisonAt
end YangMills.Construction.ResponseInTheExpansion
end
