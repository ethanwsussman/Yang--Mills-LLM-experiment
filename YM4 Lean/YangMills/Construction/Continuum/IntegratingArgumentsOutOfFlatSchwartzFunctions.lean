import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
def IntegrateOutBounds : Prop :=
  ∀ n k : ℕ, 0 < n → 4 < k → ∀ φ ∈ flatSchwartzSet n, ∀ A : Finset (Fin n),
    (A.card < n →
      (1 ≤ A.card → ∀ y : PointTuple (n - A.card), y ∈ integrableFibers A φ) ∧
      integrateOut A φ ∈ flatSchwartzSet (n - A.card) ∧
      weightedSeminorm (k * (n - A.card)) (integrateOut A φ) ≤
        weightIntegral k ^ A.card * weightedSeminorm (k * n) φ) ∧
    Integrable φ ∧
    ENNReal.ofReal ‖∫ x, φ x‖ ≤ weightIntegral k ^ n * weightedSeminorm (k * n) φ
end YangMills.Construction.TestSpaces
end
