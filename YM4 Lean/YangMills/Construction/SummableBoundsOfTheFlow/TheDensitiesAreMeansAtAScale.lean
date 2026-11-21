import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
open BlockAverages ColdStepAtMirrorFrames
def DensitiesAreRescaledMeans : Prop :=
  EventuallyOrdered fun T => ∃ l₀ : ℝ, 0 < l₀ ∧
    ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (f : LocalFamily) (l : ℝ) (Y : F.Cell),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 < l → l ≤ l₀ →
      (∀ θ : ℝ, cutoffMean T.ballRadius T.p
          (fun η => θ * stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f 0 V η +
            (1 - θ) * totalQuadratic T.lam (l⁻¹ ^ 2) η)
          (fun η => cellExponent true T.a T.ρA (l⁻¹ ^ 2) 0 Y V η - cellQuadratic T.lam (l⁻¹ ^ 2) Y η) =
        observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V) ∧
      (∀ θ : ℝ, cutoffMean T.ballRadius T.p (stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f θ V)
          (fun η => cellCentredExpansion true T.a T.ρA 0 f Y η V) =
        observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) l V) ∧
      interactionDensity true T.a T.ρA T.ballRadius T.lam (l⁻¹ ^ 2) 0 T.p f Y V =
        -∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V ∧
      expansionDensity true T.a T.ρA T.ballRadius (l⁻¹ ^ 2) 0 T.p f Y V =
        ∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) l V
end YangMills.Construction.ScaledVariables
end
