import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ObservableOfTheFrameGap
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
open BlockAverages ColdStepAtMirrorFrames
def gapObservableMean (P : StepParameters) (x s : ℝ) (φ : LocalFamily) {F : BlockFrame} (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  ballExpectation (cutoffFactor P.ballRadius P.p) (Interpolation.familyLawExponent s P.a P.chainParams.ρA x (frameRadius x) φ V)
    (Interpolation.blockGapObservable P.a P.chainParams.ρA (frameRadius x) P.p Y V)
end YangMills.Construction.BlockMeans
end
