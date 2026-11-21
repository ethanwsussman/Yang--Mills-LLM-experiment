import YangMills.Construction.SummableBoundsOfTheFlow.FinerExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.NumbersOfFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps TorusFields
namespace FamilyNorms
structure StepImagePieces (p : StepParameters) (t : ℕ) (x ε C₀ Na M b₀ d₀ : ℝ) (Dp : TorusFunctional)
    (f' c m e g a : LocalDensity) : Prop where
  admissible : p.Admissible
  E_le_E₃ : p.E ≤ p.E₃
  one_le_x : 1 ≤ x
  ε_pos : 0 < ε
  C₀_nonneg : 0 ≤ C₀
  Na_nonneg : 0 ≤ Na
  small_constants : (C₀ + 3 * C₀ * Na) * x ^ (-(1 / 2 : ℝ)) ≤ 1 / 16
  abs_d₀_le : |d₀| ≤ M
  log_density_eq : ∀ n [NeZero n], p.n₀ ≤ n → ∀ V : TorusField n, IsCold p.threshold V →
    Real.log (Dp n V) - Real.log (Dp n (trivialField n)) +
        x * actionAtLevel p.coupling p.side (t + 1) Finset.univ V =
      ∑ y, centered (c + m + e + g) n y V
  reference_norm : IsNormBoundedFamily p (p.E / 2) (p.E₃ / 2) f'
  reference_curvatureForm : HasVanishingCurvatureForm f'
  excess_norm : IsNormBoundedFamily p (C₀ * x ^ (-(3 / 4 : ℝ))) (C₀ * x ^ (-(3 / 4 : ℝ))) (c - f' - b₀ • a)
  mean_norm : IsNormBoundedFamily p (ε / 16 + C₀ * ε * x ^ (-(1 / 2 : ℝ)))
    (thirdOrderSize p (ε / 16) + C₀ * ε * x ^ (-(1 / 2 : ℝ))) m
  frameChange_norm : IsNormBoundedFamily p (C₀ * x ^ (-(2 : ℝ))) (C₀ * x ^ (-(2 : ℝ))) e
  gas_norm : IsNormBoundedFamily p (C₀ * x ^ (-(2 : ℝ))) (C₀ * x ^ (-(2 : ℝ))) g
  share_curvatureFamily : IsCurvatureFamily p Na a
  share_invariant : SumInvariantUnderIsometries p a
  share_sum : ∀ n [NeZero n], p.n₀ ≤ n → ∀ V : TorusField n, IsCold p.threshold V →
    ∑ y, centered a n y V = actionAtLevel p.coupling p.side (t + 1) Finset.univ V
  share_curvatureForm : HasCurvatureForm a 1
  value_c : ∃ v, HasUnitPlaneValue c v ∧ |v - (b₀ + d₀ / x)| ≤ C₀ * x ^ (-(3 / 2 : ℝ))
  value_m : ∃ v, HasUnitPlaneValue m v ∧ |v| ≤ C₀ * ε * x ^ (-(1 / 2 : ℝ))
  value_e : ∃ v, HasUnitPlaneValue e v ∧ |v| ≤ C₀ * x ^ (-(2 : ℝ))
  value_g : ∃ v, HasUnitPlaneValue g v ∧ |v| ≤ C₀ * x ^ (-(2 : ℝ))
def imageTilt (b₀ b : ℝ) (f' c m e g a : LocalDensity) : LocalDensity :=
  (c - f' - b₀ • a) + m + e + g + (-(b - b₀)) • a
def imageTiltConstant (C₀ Na M : ℝ) : ℝ := 3 * C₀ + Na * M + 3 * C₀ * Na
def imageTiltStatement : Prop :=
  ∀ (p : StepParameters) (t : ℕ) (x x' ε C₀ Na M b₀ d₀ : ℝ) (Dp : TorusFunctional)
    (f' c m e g a : LocalDensity),
    StepImagePieces p t x ε C₀ Na M b₀ d₀ Dp f' c m e g a → HasExpansion p (t + 1) x' Dp →
    IsCurvatureFreeTilt p (t + 1) x' Dp f' (imageTilt b₀ (x - x') f' c m e g a)
        (ε / 8 + imageTiltConstant C₀ Na M * x ^ (-(3 / 4 : ℝ))) ∧
      |x' - (x - b₀ - d₀ / x)| ≤ 3 * C₀ * (x ^ (-(1 / 2 : ℝ)) * ε + x ^ (-(3 / 2 : ℝ)))
end FamilyNorms
end YangMills.Construction
end
