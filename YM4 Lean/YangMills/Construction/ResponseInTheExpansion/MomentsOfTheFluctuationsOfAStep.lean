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
def stepDeviationMomentsAt : Prop :=
  ∀ q : ℕ, ∃ C x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ)
    (o : TorusSite n) (Z : Finset (TorusBond (n * (Tb.stepParameters y).side))),
    IsLocalChainAbove Tb y T β k n nn x₀ → (Tb.stepParameters y).side ∣ n →
    j < 2 * localChainDepth (Tb.stepParameters y) β k →
    Z ⊆ chartBondsInBlocks (Tb.stepParameters y).side
      (supBall o ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8)) →
    (Z.card : ℝ) ≤ flowCouplings (Tb.stepParameters y) β k →
    (∀ b ∈ Z, Integrable (Set.indicator
        {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
        (fun u' => ‖(stepDeviation T (k + j) u'.2.2.1
          (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1) b : Quaternion ℝ)‖ ^ q))
      (markedSampleLaw T β (k + j + 1) n)) ∧
    Integrable (Set.indicator
        {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
        (fun u' => finsetSupNonneg Z (fun b =>
          ‖(stepDeviation T (k + j) u'.2.2.1
            (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1) b : Quaternion ℝ)‖) ^ q))
      (markedSampleLaw T β (k + j + 1) n) ∧
    ∀ᵐ u ∂(markedSampleLaw T β (k + j + 1) n),
      Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) →
      (∀ b ∈ Z, ((markedSampleLaw T β (k + j + 1) n)[Set.indicator
            {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
              StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
            (fun u' => ‖(stepDeviation T (k + j) u'.2.2.1
              (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1) b : Quaternion ℝ)‖ ^ q) |
          stageSigma T (k + j + 1) n]) u ≤ (C * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ q) ∧
      ((markedSampleLaw T β (k + j + 1) n)[Set.indicator
            {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
              StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
            (fun u' => finsetSupNonneg Z (fun b =>
              ‖(stepDeviation T (k + j) u'.2.2.1
                (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1) b : Quaternion ℝ)‖) ^ q) |
          stageSigma T (k + j + 1) n]) u ≤
        (C * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 1 / 1000)) ^ q
def stepDeviationMomentsStatement : Prop := HoldsOnParameterFamilies stepDeviationMomentsAt
end YangMills.Construction.ResponseInTheExpansion
end
