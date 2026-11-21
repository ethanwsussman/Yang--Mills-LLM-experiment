import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeight
import YangMills.Construction.TransferOperators.DecayNumbersAdmissiblePairsAndTheOperatorHat
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def CharCoeffRatioBoundStatement : Prop :=
  ∀ (β : ℝ) (K : Type) [Finite K] (d : K → ℕ) (m m' : K → HalfNatural),
    0 < β → IsDegreeCompatible d m m' →
    ‖charCoeffRatio β m m'‖ ≤
        (∏ᶠ b, (besselRatioBound β * (1 + (d b : ℝ))) ^ d b) *
          (1 + weightSum m') ^ degreeTotal d ∧
      1 + weightSum m' ≤ (1 + (degreeTotal d : ℝ) / 2) * (1 + weightSum m)
end YangMills.Construction.SpinHarmonics
end
