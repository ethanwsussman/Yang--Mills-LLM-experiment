import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def CurvatureCoefficientOfSum : Prop :=
  ∀ ℓ : StepParameters, ℓ.Admissible → ∀ (Cs CE ε e x : ℝ) (u s τ g : LocalDensity), 0 ≤ Cs → 0 ≤ CE → 0 ≤ ε →
    0 ≤ e → 0 < x →
    ExpansionDensityBounds ℓ Cs CE ε e x u s τ g → SumInvariantUnderIsometries ℓ (sumOfFour u s τ g) →
    CE * x ^ (-(1 / 2 : ℝ)) + (ε + e) * potentialWeightSum ℓ.rt ℓ.n₁ ≤ 1 →
    HasLimitSecondDeriv u ∧ HasLimitSecondDeriv s ∧ HasLimitSecondDeriv τ ∧ HasLimitSecondDeriv g ∧
    curvatureCoefficient (sumOfFour u s τ g) =
      curvatureCoefficient u + curvatureCoefficient s + curvatureCoefficient τ + curvatureCoefficient g ∧
    HasCurvatureForm (sumOfFour u s τ g) (curvatureCoefficient (sumOfFour u s τ g)) ∧
    |curvatureCoefficient (sumOfFour u s τ g)| ≤ baseConstant Cs ℓ.rt
end YangMills.Construction.TorusLumps
end
