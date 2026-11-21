import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Interpolation
def contourKernelDerivBound : Prop :=
  ∃ D : StepParameters → ℕ → ℕ → ℝ, (∀ T l j, 0 < D T l j) ∧
    EventuallyInParameters fun T => ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ)
      (η : StepVariable (finiteCells F)), T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ (c₀ : F.Site F.top × Fin 4) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
        (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
        (X : Fin j → imaginaryQuaternions),
        1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
        ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => Real.log ‖contourAverage
          (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' ζ) c₀‖) η V b u c X) 0 ∧
        |jointMixedDeriv (fun ζ V' => Real.log ‖contourAverage
          (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' ζ) c₀‖) η V b u c X| ≤
          D (rateParameters T) l j * Real.exp (-(2 ^ 8 * T.κ *
            cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c)))
end Interpolation
end YangMills.Construction
end
