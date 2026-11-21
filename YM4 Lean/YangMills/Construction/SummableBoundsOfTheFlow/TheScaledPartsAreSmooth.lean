import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ScaledVariables
namespace StepDensities
def rescaledPartsSmoothStatement : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ K : ℝ, 0 < l₀ ∧ 0 ≤ K ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
      T.IsBoundedFamilyOrderSix e t f →
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      IsSmoothObservable T.κ T.ballRadius l₁ K Y V
        (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) ∧
      IsSmoothObservable T.κ T.ballRadius l₁ K Y V (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ)
end StepDensities
end YangMills.Construction
end
