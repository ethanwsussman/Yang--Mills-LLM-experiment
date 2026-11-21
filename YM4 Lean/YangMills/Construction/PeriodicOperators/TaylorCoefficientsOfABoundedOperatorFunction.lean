import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import YangMills.Construction.Towers.AveragesAreContractions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CauchyTaylorBounds
open YangMills.Construction.Tower.SmoothingContraction (OpNormLE)
section Setting
variable (E P Q : PeriodicData)
structure IsFieldNorm (N : (E.Carrier → ℂ) → ℝ≥0∞) : Prop where
  smul_eq : ∀ (c : ℂ) (f : E.Carrier → ℂ), N (c • f) = ENNReal.ofReal ‖c‖ * N f
  add_le : ∀ f g : E.Carrier → ℂ, N (f + g) ≤ N f + N g
  bounded_of_lt_top : ∀ f : E.Carrier → ℂ, N f < ∞ → ∃ r : ℝ, ∀ k, ‖f k‖ ≤ r
structure BoundedOnBall (T : (E.Carrier → ℂ) → Q.Carrier → P.Carrier → ℂ)
    (N : (E.Carrier → ℂ) → ℝ≥0∞) (ρ C : ℝ) : Prop where
  opNorm_le : ∀ f : E.Carrier → ℂ, N f < ENNReal.ofReal ρ → OpNormLE P Q (T f) C
  differentiableOn_line : ∀ f : E.Carrier → ℂ, N f < ∞ → ∀ (j : Q.Carrier) (i : P.Carrier),
    DifferentiableOn ℂ (fun σ : ℂ => T (σ • f) j i) {σ | N (σ • f) < ENNReal.ofReal ρ}
end Setting
def CoeffBounds : Prop :=
  ∀ E P Q : PeriodicData, IsPeriodic E → IsPeriodic P → IsPeriodic Q →
    ∀ T : (E.Carrier → ℂ) → Q.Carrier → P.Carrier → ℂ, IsLocalOpFun E P Q T →
    ∀ (N : (E.Carrier → ℂ) → ℝ≥0∞) (ρ C : ℝ), 0 < ρ → 0 ≤ C → IsFieldNorm E N →
      BoundedOnBall E P Q T N ρ C →
      ∀ f g : E.Carrier → ℂ, N f < ∞ → N g < ∞ →
        OpNormLE P Q (coeffOne E P Q T f) (C * ρ⁻¹ * (N f).toReal) ∧
          OpNormLE P Q (coeffTwo E P Q T f g)
            (4 * C * ρ⁻¹ ^ 2 * (N f).toReal * (N g).toReal)
end YangMills.Construction.PeriodicOperators.CauchyTaylorBounds
end
