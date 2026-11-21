import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def nearlyCollinearPositivityStatement : Prop :=
  ∀ (φ : Fin 4 → TestFunctions.EuclideanFourSpace → ℝ) (R d : ℝ), 0 < d → IsSupTestFamily R d φ →
    (∀ i x, 0 ≤ φ i x) → (∀ i, ∃ x, φ i x ≠ 0) →
    ∀ e : TestFunctions.EuclideanFourSpace, ‖e‖ = 1 →
    (∀ i j, i ≠ j → ∀ x ∈ tsupport (φ i), ∀ y ∈ tsupport (φ j),
      63 / 64 * ‖x - y‖ ^ 2 ≤ inner ℝ (x - y) e ^ 2) →
    (∀ x : Fin 4 → TestFunctions.EuclideanFourSpace, (∀ i, x i ∈ tsupport (φ i)) →
      ∀ σ ∈ CyclicFormula.unorientedCyclicOrders 4,
      3 ≤ CyclicFormula.exteriorSquareTrace
        (List.ofFn fun c : Fin 4 => CyclicFormula.inversionMatrix (x (σ c) - x (σ (c + 1)))).prod) ∧
    0 < CyclicFormula.cyclicMomentFormula 4 φ
end YangMills.Construction.MomentLaw
end
