import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapObservable
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
namespace BlockMeans
def GapMeansInvariantAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
    (∀ (Y : F.Cell) (γ : F.Cell → UnitQuaternion), gapObservableMean T x s φ Y (gaugeTransform γ V) = gapObservableMean T x s φ Y V) ∧
    ∀ Y h : F.Cell, gapObservableMean T x s φ (Y + h) (translateField h V) = gapObservableMean T x s φ Y V
def gapMeansInvariant : Prop := EventuallyInParameters GapMeansInvariantAt
end BlockMeans
end YangMills.Construction
end
