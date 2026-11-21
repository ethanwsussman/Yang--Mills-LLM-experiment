import YangMills.Construction.ClusterExpansionOfAStep.FormsOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def densitiesLessMultiple (u s τ g a : LocalDensity) (b : ℝ) : LocalDensity :=
  fun n y W => sumOfFour u s τ g n y W - b * a n y W
structure ColdExpansionHypotheses (ℓ : StepParameters) (t : ℕ) (x b Cs CE ε e Na : ℝ) (Dp : TorusFunctional)
    (u s τ g a : LocalDensity) : Prop where
  admissible : ℓ.Admissible
  densityBounds : ExpansionDensityBounds ℓ Cs CE ε e x u s τ g
  positive : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V → 0 < Dp n V
  log_eq : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
    ∑ y, centered (sumOfFour u s τ g) n y V =
      Real.log (Dp n V) - Real.log (Dp n (trivialField n)) +
        x * actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ V
  family : IsCurvatureFamily ℓ (weightGrowthSup ℓ.rt ℓ.n₁ * Na) a
  sum_eq_action : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
    ∑ y, centered a n y V = actionAtLevel ℓ.coupling ℓ.side (t + 1) Finset.univ V
  form_sum : HasCurvatureForm (sumOfFour u s τ g) b
  form_family : HasCurvatureForm a 1
  abs_b_le : |b| ≤ baseConstant Cs ℓ.rt
  Cs_nonneg : 0 ≤ Cs
  CE_nonneg : 0 ≤ CE
  Na_nonneg : 0 ≤ Na
  x_nonneg : 0 ≤ x
  ε_nonneg : 0 ≤ ε
  e_nonneg : 0 ≤ e
  E_eq : ℓ.E = 4 * expansionConstant Cs Na ℓ.rt ℓ.n₁
  E_le : ℓ.E ≤ ℓ.E₃
  small : CE * x ^ (-(1 / 2 : ℝ)) * weightGrowthSup ℓ.rt ℓ.n₁ + 2 * ε + 2 * e ≤ ℓ.E / 64
def ColdExpansionOfDensities : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (x b Cs CE ε e Na : ℝ) (Dp : TorusFunctional) (u s τ g a : LocalDensity),
    ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a →
    ColdExpansion ℓ (t + 1) (x - b) Dp (densitiesLessMultiple u s τ g a b)
end YangMills.Construction.TorusLumps
end
