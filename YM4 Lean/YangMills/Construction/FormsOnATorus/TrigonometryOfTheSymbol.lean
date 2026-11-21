import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def latticeMomentumTrigStatement : Prop :=
  (∀ t : ℝ, |Real.cos t - 1 + t ^ 2 / 2| ≤ t ^ 4 / 2) ∧
  (∀ (p : Fin 4 → ℝ) (i j : Fin 4),
    |4 * Real.sin (p i / 2) * Real.sin (p j / 2) - p i * p j| ≤ 2 * momentumNormSq p ^ 2) ∧
  (∀ a h : Fin 4 → ℝ,
    ∑ q ∈ Finset.univ.filter (fun q : Fin 4 × Fin 4 => q.1 < q.2), (a q.1 * h q.2 - a q.2 * h q.1) ^ 2 =
      (∑ l, h l ^ 2) * (∑ l, a l ^ 2) - (∑ l, a l * h l) ^ 2) ∧
  ∀ p : Fin 4 → ℝ, p ∈ brillouinBox →
    4 / Real.pi ^ 2 * momentumNormSq p ≤ ∑ l, (2 * Real.sin (p l / 2)) ^ 2
end YangMills.Construction.LimitForms
end
