import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def bondIndicator {n : ℕ} (b : TorusBond n) : TorusBond n → ℝ := fun c => if c = b then 1 else 0
def trivialHessianPairing (a : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] (h h' : TorusBond (n * L) → ℝ) : ℝ :=
  chartRestriction L u n h ⬝ᵥ Matrix.mulVec (trivialHessian a L u n) (chartRestriction L u n h')
def reflectedHessianEntriesAt : Prop :=
  ∃ C c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ)
    (o : TorusSite n) (V : TorusField n) (g : TorusSite n → UnitQuaternion) (s : ℝ)
    (b b' : TorusBond (n * (Tb.stepParameters y).side)) (e e' : Fin 3),
    IsLocalChainAbove Tb y T β k n nn x₀ → j < localChainDepth (Tb.stepParameters y) β k → 0 ≤ s →
    IsColdOnBall (Tb.stepParameters y).threshold V o (localBlockSide (Tb.stepParameters y) β k) →
    IsNearIdentity g V o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) s →
    b ∈ StepCosts.chartBonds (Tb.stepParameters y).side n → b' ∈ StepCosts.chartBonds (Tb.stepParameters y).side n →
    parentBlock (Tb.stepParameters y).side b.1 ∈ supBall o
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
        5 / 2 * localLogScale (Tb.stepParameters y) β k) →
    parentBlock (Tb.stepParameters y).side b'.1 ∈ supBall o
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
        2 * localLogScale (Tb.stepParameters y) β k) →
    |reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
        (bondIndicator b) e ⬝ᵥ
        Matrix.mulVec (frameHessian (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).toStepSetup.frameReach
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
            (TorusFields.gaugeTransform (restrictGauge g (supBall o
              (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)))) V)))
          (reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
            (bondIndicator b') e') -
      (if e = e' then trivialHessianPairing (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n
        (bondIndicator b) (bondIndicator b') else 0)| ≤
      C * s * Real.exp (-(c * (supDist b.1 b'.1 : ℝ))) + Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))
def reflectedHessianEntriesStatement : Prop := HoldsOnParameterFamilies reflectedHessianEntriesAt
end YangMills.Construction.ResponseInTheExpansion
end
