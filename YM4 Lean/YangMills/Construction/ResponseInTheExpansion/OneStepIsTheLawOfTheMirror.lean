import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import YangMills.Construction.ResponseInTheExpansion.MirrorLawOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields TorusLumps RenormalizationStepParameters MarkedIntegrals
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def oneStepReflectedLawAt : Prop :=
  ∃ C c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (nn : ℝ) (j : ℕ)
    (o : TorusSite n) (Z : Finset (TorusBond (n * (Tb.stepParameters y).side))) (F : (↥Z × Fin 3 → ℝ) → ℝ) (B : ℝ),
    IsLocalChainAbove Tb y T β k n nn x₀ → (Tb.stepParameters y).side ∣ n →
    j < 2 * localChainDepth (Tb.stepParameters y) β k →
    Z ⊆ chartBondsInBlocks (Tb.stepParameters y).side
      (supBall o ((localBlockSide (Tb.stepParameters y) β k : ℝ) / 8)) →
    Measurable F → (∀ v, |F v| ≤ B) →
    Integrable (Set.indicator
        {u' | Disjoint (stageState T (k + j + 1) n u').2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
        (fun u' => F (imaginaryComponentsOn Z (stepDeviation T (k + j) u'.2.2.1
          (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1)))))
      (markedSampleLaw T β (k + j + 1) n) ∧
    ∀ᵐ u ∂(markedSampleLaw T β (k + j + 1) n),
      Disjoint (stageState T (k + j + 1) n u).2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) →
      |((markedSampleLaw T β (k + j + 1) n)[Set.indicator
            {u' | Disjoint (stageState T (k + j + 1) n u').2.1
                (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
              StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o u'}
            (fun u' => F (imaginaryComponentsOn Z (stepDeviation T (k + j) u'.2.2.1
              (topField (Tb.stepParameters y) (k + j) (n * (Tb.stepParameters y).side) u'.1)))) |
          stageSigma T (k + j + 1) n]) u -
        reflectedStepMean (T.stage (k + j)).toStepSetup (localBlockSide (Tb.stepParameters y) β k) o u.2.2.1
          (fun η => F (imaginaryComponentsOn Z (reflectedCoordinateAt (Tb.stepParameters y).side
            (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o η)))| ≤
      C * B * Real.exp (-(c * (localBlockSide (Tb.stepParameters y) β k : ℝ)))
def oneStepReflectedLawStatement : Prop := HoldsOnParameterFamilies oneStepReflectedLawAt
end YangMills.Construction.ResponseInTheExpansion
end
