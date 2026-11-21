import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmall
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ScaledVariables
namespace YangMills.Construction.StepDensities
def densityExcessSecondOrderStatement : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ y C : ℝ, 0 < y ∧ 0 < C ∧ ∀ (t : ℕ) (x : ℝ), y ≤ x →
    ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t) F Y) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        AreUnitVectors X →
        |bondDeriv (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t) F Y) V c X| ≤
          C * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) ∧
        |bondDeriv (densityExcess T t x F Y) V c X -
            x⁻¹ * bondDeriv (secondOrderDensityCoeff T.a T.ρA T.lam (T.localReference t) F Y) V c X| ≤
          C * x ^ (-(3 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
end YangMills.Construction.StepDensities
end
