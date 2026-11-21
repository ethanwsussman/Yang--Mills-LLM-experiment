import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages
def StepDensityThirdDeriv (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top)
      (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
      |bondDeriv (stepDensityFamily T x f F Y) V c X| ≤
        2⁻¹ ^ 6 * T.energyRatio / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
def stepDensityThirdDerivStatement : Prop := EventuallyInParameters StepDensityThirdDeriv
end ColdStepAtMirrorFrames
end YangMills.Construction
end
