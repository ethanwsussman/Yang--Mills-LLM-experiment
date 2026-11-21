import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import YangMills.Construction.TransfersOffTheWalk.ProductsAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses
def separatedMarkedMomentsStatement : Prop :=
  ∀ ℓ : YangMills.Construction.TorusLumps.StepParameters, ℓ.Admissible → ∀ T : StageTower ℓ,
    YangMills.Construction.ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn →
    T.MarksMeasurable →
    ∀ (p s n : ℕ) [NeZero n] (β : ℝ) (al : ℕ → ℝ) (κ : Fin p → ℝ) (x D : ℕ → ℝ)
      (h : Fin p → PlaquetteWeight (fineSide ℓ.side s n)),
      YangMills.Construction.TransfersOffTheWalk.SeparatedAlongTower ℓ x D s n h →
      ∫ u, ∏ i, (curvatureObservable (h i) (bottomField ℓ s n u) - κ i) ∂(markedSampleLaw T β s n) =
        ∫ u, ∏ i, (completedObservable T al s n (h i) u - κ i) ∂(markedSampleLaw T β s n)
end YangMills.Construction.ResponseInTheExpansion
end
