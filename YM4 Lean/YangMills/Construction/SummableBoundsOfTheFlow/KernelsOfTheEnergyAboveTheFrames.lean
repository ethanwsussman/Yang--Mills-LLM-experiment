import YangMills.Construction.SummableBoundsOfTheFlow.TransportAtSixDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
def EnergyKernelBounds : Prop :=
  ∃ D : StepParameters → ℕ → ℕ → ℝ, (∀ T l j, 0 < D T l j) ∧
    EventuallyInParameters fun T => ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ)
      (η : StepVariable (finiteCells F)), T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
        (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
        2 ≤ l → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
        ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' =>
          chartedEnergy T.a (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V' ζ) V') η V b u c X) 0 ∧
        |jointMixedDeriv (fun ζ V' =>
          chartedEnergy T.a (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V' ζ) V') η V b u c X| ≤
          D (rateParameters T) l j *
            Real.exp (-(T.chainParams.δ₂ * cellSetDiameter (chordBondCells b ∪ topBondCells c)))
end YangMills.Construction.Interpolation
end
