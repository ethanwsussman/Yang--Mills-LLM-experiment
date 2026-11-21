import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
def TensorSeminormBounds : Prop :=
  (∀ q r k : ℕ, 0 < q → 0 < r → 0 < k →
    ∀ φ ∈ schwartzSet q, ∀ ψ ∈ schwartzSet r,
      tensorFun φ ψ ∈ schwartzSet (q + r) ∧
      weightedSeminorm k (tensorFun φ ψ) ≤ weightedSeminorm k φ * weightedSeminorm k ψ ∧
      (VanishesToInfiniteOrderOff φ (negativeTimeLocus q) →
        VanishesToInfiniteOrderOff ψ (positiveTimeLocus r) →
        tensorFun φ ψ ∈ flatSchwartzSet (q + r))) ∧
  (∀ r k : ℕ, 0 < r → 0 < k → ∀ c : ℂ, ∀ ψ ∈ schwartzSet r,
    weightedSeminorm k (scalarTensorLeft c ψ) = ENNReal.ofReal ‖c‖ * weightedSeminorm k ψ)
end YangMills.Construction.TestSpaces
