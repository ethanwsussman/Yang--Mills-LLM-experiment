import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
open WeightedResponses
def symbolPropertiesStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb _ => ∀ c₁ C₁ : ℝ, 0 < c₁ → ∃ (c C : ℝ) (D : ℕ → ℝ), 0 < c ∧
    ∀ (k : ℕ) (Q : IntBond → IntBond → ℝ), IsLimitForm Tb.coupling Tb.coercivity c₁ C₁ Tb.side k Q →
    ((∀ (i j : Fin 4) (p : Fin 4 → ℝ), AnalyticAt ℝ (midpointSymbol Q i j) p) ∧
      (∀ (p : Fin 4 → ℝ) (ξ : Fin 4 → ℂ), p ∈ brillouinBox →
        c * momentumNormSq p * ∑ i, ‖ξ i‖ ^ 2 ≤
          (∑ i, ∑ j, (starRingEnd ℂ) (ξ i) * midpointSymbol Q i j p * ξ j).re) ∧
      ∀ (i j : Fin 4) (p : Fin 4 → ℝ), p ∈ brillouinBox →
        ‖midpointSymbol Q i j p - (if i = j then (momentumNormSq p : ℂ) else 0)‖ ≤ C * momentumNormSq p ^ 2) ∧
    (∀ (i j l : Fin 4) (d : ℕ) (p : Fin 4 → ℝ),
      ‖iteratedDeriv d (fun t : ℝ => midpointSymbol Q i j (Function.update p l t)) (p l)‖ ≤ D d) ∧
    (∀ (i j : Fin 4) (p : Fin 4 → ℝ), (midpointSymbol Q i j p).im = 0) ∧
    (∀ (i j : Fin 4) (p : Fin 4 → ℝ), midpointSymbol Q i j p = midpointSymbol Q j i p) ∧
    ∀ (i : Fin 4) (p : Fin 4 → ℝ),
      ∑ j, (midpointSymbol Q i j p - ((4 * Real.sin (p i / 2) * Real.sin (p j / 2) : ℝ) : ℂ)) *
        ((2 * Real.sin (p j / 2) : ℝ) : ℂ) = 0
end YangMills.Construction.LimitForms
end
