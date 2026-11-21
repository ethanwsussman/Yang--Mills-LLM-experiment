import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmall
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.StepDensities
def densityExcessLocalStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y C : ℝ, 0 < y ∧ 0 < C ∧ ∀ (t : ℕ) (x : ℝ), y ≤ x →
    ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
      (r : ℕ), IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      |densityExcess T t x F Y V - densityExcess T t x F' Y' V'| ≤
        C * Real.exp (-(T.κ * r / 2 ^ 7))
end YangMills.Construction.StepDensities
end
