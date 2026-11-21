import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open TorusLumps TorusFields RenormalizationStepParameters StepSettings WeightedResponses
open Classical
open MeasureTheory
def blocksNearFreeCores (L r : ℕ) [NeZero L] {n : ℕ} [NeZero n] (Z : Finset (TorusSite n)) : Finset (TorusSite n) :=
  (thickening (4 * r) (sitesInBlocks L Z)).image (parentBlock L)
def freeCoresRareStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β s → IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed → (T.stage s).nextCoupling ≤ 1.01 * (T.stage s).coupling →
    IsBlockTorusSide (Tb.stepParameters y) n →
    ∀ (m : ℝ) (o : TorusSite n),
      (markedSampleLaw T β (s + 1) n).real {u | ¬ StepAvoids T s m o u} ≤
        ((blocksNearFreeCores (Tb.stepParameters y).side (T.stage s).toStepSetup.range (supBall o m)).card : ℝ) *
          Real.exp (-(7 * Tb.gasRate * (T.stage s).coupling))
end ResponseInTheExpansion
end YangMills.Construction
end
