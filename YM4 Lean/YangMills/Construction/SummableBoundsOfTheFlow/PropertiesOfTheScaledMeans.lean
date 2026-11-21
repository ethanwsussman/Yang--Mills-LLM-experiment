import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
def ForallSmoothObservables
    (P : (T : StepParameters) → (C K l₁ : ℝ) → LocalFamily → StepLaw → (F : BlockFrame) → F.Cell →
      F.GaugeField F.top → (ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) → (k : ℕ) →
      (Fin k → F.Site F.top × Fin 4) → (Fin k → imaginaryQuaternions) → Prop) : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ C : ℝ, 0 < l₀ ∧ 0 < C ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (law : StepLaw) (K : ℝ)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → StepLaw.IsUnitWeight law → 0 ≤ K →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y Ob → AreUnitVectors X →
      P T C K l₁ f law F Y V Ob k c X
end ScaledVariables
end YangMills.Construction
end
