import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.FiniteValenceNorm
def Claim : Prop :=
  ∀ P P' : PeriodicData, IsPeriodic P → IsPeriodic P' →
    ∀ w : ℝ, (∀ a, P.weightOf a = w) → (∀ a', P'.weightOf a' = w) →
    ∀ (T : QuotHom P P') (K : P'.Carrier → P.Carrier → ℂ) (R : P'.Carrier → P.Carrier → Prop) (m : ℕ)
      (b : ℝ), 0 ≤ b →
      (∀ (n : Fin 4 → ℤ) a' a, R a' a → R (P'.translate n a') (P.translate n a)) →
      (∀ a', {a | R a' a}.encard ≤ m) → (∀ a, {a' | R a' a}.encard ≤ m) →
      (∀ a' a, ‖K a' a‖ ≤ b) → (∀ a' a, ¬ R a' a → K a' a = 0) →
      (∀ (φ : P.UnitQuot → ℂ) a',
        T φ (P'.mkQuot 1 a') = ∑' a, K a' a * φ (P.mkQuot 1 a)) →
      quotHomNorm T ≤ ENNReal.ofReal (m * b)
end YangMills.Construction.PeriodicOperators.FiniteValenceNorm
end
