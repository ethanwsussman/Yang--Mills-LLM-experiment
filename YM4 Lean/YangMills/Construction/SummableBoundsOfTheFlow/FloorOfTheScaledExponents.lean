import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
open scoped Topology
namespace ScaledVariables
def rescaledExponentFloorStatement : Prop :=
  EventuallyOrdered fun T => ∀ e : ℕ → ℝ, ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (law : StepLaw),
      T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      StepLaw.IsUnitWeight law →
      (∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 ≤ l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
        T.lam / 4 * ∑ b, ‖ζ b‖ ^ 2 - Real.sqrt T.lam / 2 * ∑ b, ‖ζ b‖ ≤
          rescaledLawExponent T.a T.ρA T.lam f l V law ζ -
            rescaledLawExponent T.a T.ρA T.lam f l V law 0) ∧
      (∀ (l : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
        stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law (l • ζ) =
          rescaledLawExponent T.a T.ρA T.lam f l V law ζ) ∧
      (∀ l : ℝ, 0 < l → l ≤ l₀ → ContinuousOn (rescaledLawExponent T.a T.ρA T.lam f l V law)
        {ζ | MemScaledBalls T.ballRadius l ζ}) ∧
      ∀ ζ : StepVariable (finiteCells F), Filter.Tendsto
        (fun l => rescaledLawExponent T.a T.ρA T.lam f l V law ζ) (𝓝[>] 0)
        (𝓝 (rescaledLawExponent T.a T.ρA T.lam f 0 V law ζ))
end ScaledVariables
end YangMills.Construction
end
