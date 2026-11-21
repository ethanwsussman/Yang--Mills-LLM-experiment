import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmall
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.StepDensities
def densitiesNearLimitsStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y C : ℝ, 0 < y ∧ 0 < C ∧ ∀ (t : ℕ) (x : ℝ), y ≤ x →
    (∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
      k ≤ 3 → AreUnitVectors X →
      |bondDeriv (densityExcess T t x F Y) V c X| ≤
        C * x⁻¹ * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))) ∧
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (centredFamily (densityExcess T t x))
      fun r => C * x ^ (-(3 / 4 : ℝ)) * Real.exp (-(T.κ / 2 ^ 9 * r))
end YangMills.Construction.StepDensities
end
