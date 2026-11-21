import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters TorusFields TorusLumps WeightedResponses LumpContours BlockAverages
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def logarithmOneStepAt : Prop :=
  ∃ C c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ)
    (o : TorusSite n) (o' : TorusSite (n * (Tb.stepParameters y).side)) (V : TorusField n)
    (W : TorusField (n * (Tb.stepParameters y).side)) (g : TorusSite n → UnitQuaternion) (s : ℝ),
    IsLocalChainAbove Tb y T β k n nn x₀ → j < localChainDepth (Tb.stepParameters y) β k → 0 ≤ s →
    s ≤ flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ)) →
    parentBlock (Tb.stepParameters y).side o' = o →
    IsColdOnBall (Tb.stepParameters y).threshold V o (localBlockSide (Tb.stepParameters y) β k) →
    IsNearIdentity g V o
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) s →
    (∀ b : TorusBond (n * (Tb.stepParameters y).side),
      b.1 ∈ supBall o' (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j) →
      ‖(minimalLog (gaugeTransform (fun x => g (parentBlock (Tb.stepParameters y).side x) *
          blockTreeGauge (Tb.stepParameters y) W x) W b) : Quaternion ℝ)‖ ≤ s) →
    ∀ b : TorusBond (n * (Tb.stepParameters y).side),
      b.1 ∈ supBall o' (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j) →
      ‖((minimalLog (gaugeTransform (fun x => g (parentBlock (Tb.stepParameters y).side x) *
            blockTreeGauge (Tb.stepParameters y) W x) W b) -
          responseOfLieForm (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
            (Tb.stepParameters y).side (k + j)
            (ballLog g V o (ballRadius (Tb.stepParameters y).side nn
              (localLogScale (Tb.stepParameters y) β k) (j + 1))) b -
          deviationInGauge T (k + j) g
            (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
              3 * localLogScale (Tb.stepParameters y) β k)) V W b : imaginaryQuaternions) :
          Quaternion ℝ)‖ ≤ C * (s ^ 2 + Real.exp (-(c * localLogScale (Tb.stepParameters y) β k)))
def logarithmOneStepStatement : Prop := HoldsOnParameterFamilies logarithmOneStepAt
end YangMills.Construction.ResponseInTheExpansion
end
