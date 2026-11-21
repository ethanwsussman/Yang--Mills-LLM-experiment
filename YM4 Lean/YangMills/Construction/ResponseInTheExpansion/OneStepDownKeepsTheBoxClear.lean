import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses TorusFields TorusLumps StepSettings RenormalizationStepParameters
  MarkedIntegrals StepCosts
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def descentKeepsBallClearAt : Prop :=
  ∃ x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ) (o : TorusSite n),
    IsLocalChainAbove Tb y T β k n nn x₀ → (Tb.stepParameters y).side ∣ n →
    j < 2 * localChainDepth (Tb.stepParameters y) β k →
    ∀ᵐ u ∂(markedSampleLaw T β (k + j + 1) n),
      Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) →
      IsColdOnBall (Tb.stepParameters y).threshold u.2.2.1 o (localBlockSide (Tb.stepParameters y) β k) ∧
      (StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u →
        (∀ o' : TorusSite (n * (Tb.stepParameters y).side), parentBlock (Tb.stepParameters y).side o' = o →
          Disjoint (stageState T (k + j) (n * (Tb.stepParameters y).side) u.1).2.1
            (supBall o' (localBlockSide (Tb.stepParameters y) β k))) ∧
        ∀ b ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall o (localBlockSide (Tb.stepParameters y) β k)),
          b ∉ (show Finset (TorusBond (n * (Tb.stepParameters y).side)) from u.2.2.2) ∧
          ‖(stepDeviation T (k + j) u.2.2.1
              (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u.1) b : Quaternion ℝ)‖ <
            (Tb.stepParameters y).threshold / 64)
def descentKeepsBallClearStatement : Prop := HoldsOnParameterFamilies descentKeepsBallClearAt
end YangMills.Construction.ResponseInTheExpansion
end
