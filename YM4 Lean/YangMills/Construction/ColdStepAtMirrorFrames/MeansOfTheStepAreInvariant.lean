import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def StepMeansInvariantAt (T : StepParameters) : Prop :=
  T.ForAllSteps fun t x f => ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
    IsSmallCurvature (5 / 4 * T.σ) V →
    (∀ (Y : F.Cell) (γ : F.Cell → UnitQuaternion),
      T.interactionFamily x f F Y (gaugeTransform γ V) = T.interactionFamily x f F Y V ∧
      T.expansionFamily x f F Y (gaugeTransform γ V) = T.expansionFamily x f F Y V) ∧
    ∀ Y h : F.Cell, T.interactionFamily x f F (Y + h) (translateField h V) = T.interactionFamily x f F Y V ∧
      T.expansionFamily x f F (Y + h) (translateField h V) = T.expansionFamily x f F Y V
def stepMeansInvariantStatement : Prop := EventuallyInParameters StepMeansInvariantAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
