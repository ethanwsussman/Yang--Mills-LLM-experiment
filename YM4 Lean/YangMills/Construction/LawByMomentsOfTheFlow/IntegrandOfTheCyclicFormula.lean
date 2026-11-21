import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CyclicFormula
open TestFunctions
def CycleIntegrandIntegrable : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ (R d : ℝ) (φ : Fin n → EuclideanFourSpace → ℝ), 0 < d →
    IsSeparatedLipschitzFamily R d φ →
    ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun x : Fin n → EuclideanFourSpace => (∏ i, φ i (x i)) * cycleKernel σ x)
end YangMills.Construction.CyclicFormula
end
