import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open StepSettings TorusFields TorusLumps WeightedResponses ResponseInTheExpansion ColdStepAtMirrorFrames
open Classical
def freeCoresRareGivenStateStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β s → IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed → (T.stage s).nextCoupling ≤ 1.01 * (T.stage s).coupling →
    IsBlockTorusSide (Tb.stepParameters y) n →
    ∀ (m : ℝ) (o : TorusSite n), MeasurableSet {u | ¬ StepAvoids T s m o u} ∧ ∀ᵐ u ∂(markedSampleLaw T β (s + 1) n),
      ((markedSampleLaw T β (s + 1) n)[{u | ¬ StepAvoids T s m o u}.indicator (fun _ => (1 : ℝ)) | stageSigma T (s + 1) n]) u ≤
        ((blocksNearFreeCores (Tb.stepParameters y).side (T.stage s).toStepSetup.range (supBall o m)).card : ℝ) *
          Real.exp (-(7 * Tb.gasRate * (T.stage s).coupling))
end YangMills.Construction.MomentLaw
end
