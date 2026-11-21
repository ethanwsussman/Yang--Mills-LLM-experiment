import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages StepSettings TorusFields ColdStepAtMirrorFrames
def StepSettings.StepSetup.bondGaussian (R : StepSetup) (lam : ℝ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin 3),
    cutoffFactor R.ballRadius R.barrierFn (coordNorm z) * Real.exp (-(R.coupling * lam / 2 * ‖z‖ ^ 2))
namespace ClusterExpansionOfAStep
def CutPotentialIntegralFactors : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (s : ChartSetting R n) (lam : ℝ) (N : Finset (TorusSite n)),
    (∫ η, cutoffProd η * Real.exp (-(s.restrictedSplit lam (s.freeNear N)).potential η)) =
      (∫ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3),
        (∏ b, cutoffFactor R.ballRadius R.barrierFn (coordNorm (ζ b))) *
          Real.exp (-s.potential (s.extendByZero N ζ))) *
      R.bondGaussian lam ^ (Finset.univ \ s.freeNear N).card
end ClusterExpansionOfAStep
end YangMills.Construction
end
