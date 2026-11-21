import YangMills.Construction.Continuum.TraceOfARingOfPropagators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeRingKernels
variable {n : ℕ}
def weightedOnSupports (f : Fin n → (Fin 4 → ℝ) → ℝ) (k : (Fin n → Fin 4 → ℝ) → ℝ) :
    (Fin n → Fin 4 → ℝ) → ℝ :=
  (PropagatorRings.supportBox f).indicator fun x => (∏ j, f j (x j)) * k x
theorem weightedOnSupports_cyclicTrace (σ : Fin n → Fin n) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    weightedOnSupports f (cyclicTrace σ) =
      (PropagatorRings.supportBox f).indicator (PropagatorRings.cyclicIntegrand σ f) :=
  rfl
end YangMills.Construction.FreeRingKernels
end
