import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import YangMills.Construction.ResponseInTheExpansion.TwoSumsOfScoresAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusLumps TorusFields StepCosts PeriodicLattice WeightedResponses ColdStepAtMirrorFrames
def TwoPointByTotalCovarianceStatement : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (weights : ℕ → ℝ) (s n : ℕ) [NeZero n],
      IsProbabilityMeasure (markedSampleLaw T β s n) ∧ stageSigma T s n ≤ markedSampleMeasurableSpace ℓ s n ∧
      Measure.map (bottomField ℓ s n) (markedSampleLaw T β s n) = wilsonLaw β (fineSide ℓ.side s n) ∧
      Measure.map (forgetMarks ℓ s n) (markedSampleLaw T β s n) =
        chainJointLaw ℓ β (fun j => (T.stage j).coupling) s n ∧
      (∀ h₁ h₂ : PlaquetteWeight (fineSide ℓ.side (s + 1) n),
        ∫ u, sourceTerm T weights s n h₁ u * sourceTerm T weights s n h₂ u ∂(markedSampleLaw T β (s + 1) n) =
          ∫ a, (ℓ.coupling * weights s) ^ 2 * ∑ c : TorusBond n,
            bondBlockMean ℓ.side (s + 1) n h₁ c * bondBlockMean ℓ.side (s + 1) n h₂ c *
            ∑ b : BaseChoice ℓ.side n, ∫ V : TorusField n,
              bondScoreVariance ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) a) b c *
                stepTransitionDensity ℓ (T.stage s).coupling (topField ℓ s (n * ℓ.side) a) b V ∂(fieldHaar n)
            ∂(markedSampleLaw T β s (n * ℓ.side))) ∧
      ∀ f₁ f₂ : PlaquetteWeight (fineSide ℓ.side s n),
        cov[curvatureObservable f₁, curvatureObservable f₂; wilsonLaw β (fineSide ℓ.side s n)] =
          cov[response T β weights s n f₁, response T β weights s n f₂; markedSampleLaw T β s n] +
            covarianceSum T β weights s n f₁ f₂
end ResponseInTheExpansion
end YangMills.Construction
end
