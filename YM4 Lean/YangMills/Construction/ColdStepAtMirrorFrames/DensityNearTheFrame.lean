import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
open BlockAverages
def StepDensityNearFrame (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V →
      |stepDensityFamily T x f F Y V - expansionAtFrameFamily T false x f F Y V| ≤ T.CE * x ^ (-(1 / 2 : ℝ)) ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
        AreUnitVectors X →
        |bondDeriv (stepDensityFamily T x f F Y) V c X - bondDeriv (expansionAtFrameFamily T false x f F Y) V c X| ≤
          T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
def stepDensityNearFrameStatement : Prop := EventuallyInParameters StepDensityNearFrame
end ColdStepAtMirrorFrames
end YangMills.Construction
end
