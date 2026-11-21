import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity TorusFields
namespace SlopeCoefficient
def stepLogAmplitude {F : BlockFrame} (g r : ℝ) (A : F.GaugeField F.top) : ℝ :=
  -(1 / 2) * Real.log (chartedHessian g r A 0).det +
    (∑ e : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame true g r 0 A 0 e.1.1 e.1.2)) +
    3 / 2 * ∑ c ∈ innerBonds (finiteCells F) F.top, Real.log ‖contourAverage (fieldAboveFrame true g r 0 A 0) c‖
def stepGaugeTotal (g r : ℝ) (L t : ℕ) : GaugeTotal := fun n A =>
  stepLogAmplitude (F := torusFrame L t n) g r (readAtLevel (torusFrame L t n) (torusFrame L t n).top A) -
    stepLogAmplitude (F := torusFrame L t n) g r (readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n))
def AreStepSlopeCoefficients (g : ℝ) (L : ℕ) (s : ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (r : ℝ), 0 < r → r ≤ 1 → HasSlopeCoefficient Filter.atTop (stepGaugeTotal g r L t) (s t)
end SlopeCoefficient
end YangMills.Construction
end
