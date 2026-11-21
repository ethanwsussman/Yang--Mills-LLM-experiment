import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
def blockKernelBoundsStatement : Prop :=
  ∃ D : StepParameters → ℕ → ℕ → ℝ, (∀ T l j, 0 < D T l j) ∧
    EventuallyInParameters fun T => ∀ (x : ℝ) (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ)
      (η : StepVariable (finiteCells F)), T.coupling ≤ x → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
        (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
        (X : Fin j → imaginaryQuaternions),
        1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
        (∀ Y : F.Cell, HasDecayingKernelAt
          (fun ζ V' => cellEnergyShare T.a Y (interpolatedCoords s T.a T.chainParams.ρA (frameRadius x) V' ζ) V')
          (D (rateParameters T) l j) (2 ^ 7 * T.κ) {Y} η V b u c X) ∧
        ∀ y : F.Site F.depth, HasDecayingKernelAt
          (fun ζ V' => minimalSiteShare T.a y (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V' ζ))
          (D (rateParameters T) l j) (2 ^ 7 * T.κ) {enclosingCell y} η V b u c X
end ResponseInTheExpansion
end YangMills.Construction
end
