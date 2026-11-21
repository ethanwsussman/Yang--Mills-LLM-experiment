import YangMills.Construction.FormsOnATorus.KernelOfTheLatticeSymbol
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open WeightedResponses RenormalizationStepParameters
def momentumSymbolMatrix (Q : IntBond → IntBond → ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => midpointSymbol Q i j p
def inverseSymbolDefect (Q : IntBond → IntBond → ℝ) (i j : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  (momentumSymbolMatrix Q p)⁻¹ i j - (if i = j then ((latticeSineNormSq p)⁻¹ : ℂ) else 0)
def inverseSymbolOrdersStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ Cs : ℕ → ℝ, ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ),
    IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q → ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      IsUnit (momentumSymbolMatrix Q p).det ∧
      (∀ d : ℕ, ContDiffAt ℝ d (fun q => (momentumSymbolMatrix Q q)⁻¹ i j) p) ∧
      ∀ (l : Fin 4) (d : ℕ),
        ‖iteratedDeriv d (fun t : ℝ => (momentumSymbolMatrix Q (Function.update p l t))⁻¹ i j) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-2 - (d : ℤ)) ∧
        ‖iteratedDeriv d (fun t : ℝ => inverseSymbolDefect Q i j (Function.update p l t)) (p l)‖ ≤
          Cs d * Real.sqrt (momentumNormSq p) ^ (-1 - (d : ℤ))
end YangMills.Construction.LimitForms
end
