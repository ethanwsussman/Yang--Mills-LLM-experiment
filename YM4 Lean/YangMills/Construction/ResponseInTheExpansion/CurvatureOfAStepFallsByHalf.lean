import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.MarkedIntegrals YangMills.Construction.WeightedResponses
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def curvatureHalvesAt : Prop :=
  ∃ C N₀ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ) (o : TorusSite n)
    (V : TorusField n),
    IsLocalChainAbove Tb y T β k n nn x₀ → j < 2 * localChainDepth (Tb.stepParameters y) β k →
    IsColdOnBall (Tb.stepParameters y).threshold V o (localBlockSide (Tb.stepParameters y) β k) →
    (∀ b ∈ StepCosts.chartBonds (Tb.stepParameters y).side n,
      supBall (parentBlock (Tb.stepParameters y).side b.1) (localLogScale (Tb.stepParameters y) β k) ⊆
        supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) →
      ‖(StepCosts.frameCoord (Tb.stepParameters y) (T.stage (k + j)).anchorRadius (k + j)
          (T.stage (k + j)).toStepSetup.frameReach V b : Quaternion ℝ)‖ ≤
        N₀ * maxCurvatureOnBall V o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) +
          C * Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))) ∧
    ∀ (W : TorusField (n * (Tb.stepParameters y).side)) (o' : TorusSite (n * (Tb.stepParameters y).side)),
      parentBlock (Tb.stepParameters y).side o' = o →
      (∀ b ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall o (localBlockSide (Tb.stepParameters y) β k)),
        ‖(stepDeviation T (k + j) V W b : Quaternion ℝ)‖ < (Tb.stepParameters y).threshold / 64) →
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      maxCurvatureOnBall W o' (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j + e) ≤
        (1 / 2) * maxCurvatureOnBall V o
            (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) + e) +
          4 * maxDeviationOnBall T (k + j) V W o
            ((ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j + e) /
              ((Tb.stepParameters y).side : ℝ) + 2) +
          C * Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))
def curvatureHalvesStatement : Prop := HoldsOnParameterFamilies curvatureHalvesAt
end YangMills.Construction.ResponseInTheExpansion
end
