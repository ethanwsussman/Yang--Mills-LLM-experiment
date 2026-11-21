import YangMills.Construction.PeriodicOperators.TracesOfKernelsAtUnitFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LogDetTraces
open LogDetSecondDerivs UnitFieldTraces
def Claim : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ (A : (P.Carrier → ℂ) → Q.Carrier → Q.Carrier → ℂ) (r Rad : ℝ), IsLocalWith P Q Q A r Rad →
    ∀ L : ℕ, 0 < L → 4 * Rad < L → IsUnit (LogDetSecondDerivs.quotOperator P Q A L 0) →
    ∀ (n : ℕ) (σ : Fin n ≃ P.QuotMod L) (u v : P.QuotMod L → ℂ),
      logDetSecondDeriv P Q A σ u v = quotTraceDefect P Q A L u v
end YangMills.Construction.PeriodicOperators.LogDetTraces
end
