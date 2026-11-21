import YangMills.Construction.Torus.CutOffsOnAProductOfOpenSetsOfFourSpace
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Torus.FourierBox
def WeightedCoeffSumBound : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ : ℝ), 1 ≤ n → 0 < ρ →
    ∀ F ∈ AmbientPoints.testFns (fundamentalBoxPow s n (4 * ρ)),
      Summable (fun k : Fin (4 * n) → ℤ => ‖fourierCoeff (4 * ρ) F k‖ *
        ∏ i, (1 + euclidNormInt (blockOf k i) / AmbientPoints.bumpScale ρ)) ∧
      ENNReal.ofReal (∑' k : Fin (4 * n) → ℤ, ‖fourierCoeff (4 * ρ) F k‖ *
        ∏ i, (1 + euclidNormInt (blockOf k i) / AmbientPoints.bumpScale ρ)) ≤
          ENNReal.ofReal (AmbientPoints.bumpNumber n ρ) * AmbientPoints.cnNorm (5 * n + 1) F
end YangMills.Construction.Torus.FourierBox
