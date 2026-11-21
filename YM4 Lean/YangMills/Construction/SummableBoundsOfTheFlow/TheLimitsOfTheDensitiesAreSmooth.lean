import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity
namespace StepDensities
def limitDensitiesSmoothStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference →
    ∀ (t : ℕ) (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds (ReferenceDensity.stepDensity T.a T.ρA T.lam Y) V ∧
      ContDiffThreeAlongBonds (fun V' => cellCentredExpansion true T.a T.ρA 0 (T.localReference t) Y 0 V') V
end StepDensities
end YangMills.Construction
end
