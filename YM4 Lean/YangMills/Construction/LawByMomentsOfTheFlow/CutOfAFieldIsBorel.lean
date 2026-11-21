import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def cutoffMeasurableStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] (o : TorusFields.TorusSite n),
    (∀ (m : ℕ) (b : TorusFields.TorusBond n) (e : Fin 3),
      Measurable fun W : TorusFields.TorusField n => BlockAverages.imaginaryComponent e (cutoffCoords ℓ W o m b)) ∧
    ∀ r : ℝ, Measurable (boxCurvature o r : TorusFields.TorusField n → ℝ)
end YangMills.Construction.MomentLaw
end
