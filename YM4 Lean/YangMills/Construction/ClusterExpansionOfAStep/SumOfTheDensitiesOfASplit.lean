import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings TorusFields ColdStepAtMirrorFrames
def SumActivitiesEqLogIntegral : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (free : Finset (TorusBond (n * R.params.side)))
    (D : BlockDensitySplit R n free) (lam : ℝ),
    0 < R.coupling → 0 < lam → 0 < R.ballRadius → IsCutoff R.ballRadius R.barrierFn → D.IsRegular →
    Real.log (∫ η, cutoffProd η * Real.exp (-D.potential η)) = ∑ Y : TorusSite n, D.activity lam Y
end YangMills.Construction.ClusterExpansionOfAStep
end
