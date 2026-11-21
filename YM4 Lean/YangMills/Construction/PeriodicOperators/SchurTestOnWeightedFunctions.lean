import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SchurTest
def ConstantWeights : Prop :=
  ∀ (J J' : Type) (T : J' → J → ℂ) (w : J → ℝ) (w' : J' → ℝ) (a a' A B c : ℝ),
    0 < a → 0 < a' → 0 ≤ c → (∀ ι, w ι = a) → (∀ ι', w' ι' = a') →
    (∀ ι', Summable (fun ι => ‖T ι' ι‖) ∧ ∑' ι, ‖T ι' ι‖ ≤ A) →
    (∀ ι, Summable (fun ι' => ‖T ι' ι‖) ∧ ∑' ι', ‖T ι' ι‖ ≤ B) →
    a' * (A * B) ≤ c ^ 2 * a →
    (∀ f, NormSummable w f →
      (∀ ι', ApplySummableAt T f ι') ∧ NormSummable w' (applyKernel T f)) ∧
    ∀ E : Set (J → ℂ), OpNormSummable w w' E (applyKernel T) ∧
      wOpNorm w w' E (applyKernel T) ≤ ENNReal.ofReal c
def DiagonalInColour : Prop :=
  ∀ (σ σ' : Type) (T : Fin 3 × σ' → Fin 3 × σ → ℂ) (N : σ' → σ → ℝ)
    (w : Fin 3 × σ → ℝ) (w' : Fin 3 × σ' → ℝ) (a a' A B c : ℝ),
    0 < a → 0 < a' → 0 ≤ c → (∀ ι, w ι = a) → (∀ ι', w' ι' = a') →
    (∀ (b b' : Fin 3) (y : σ') (x : σ), b' ≠ b → T (b', y) (b, x) = 0) →
    (∀ (b : Fin 3) (y : σ') (x : σ), ‖T (b, y) (b, x)‖ ≤ N y x) →
    (∀ y, Summable (N y) ∧ ∑' x, N y x ≤ A) →
    (∀ x, Summable (fun y => N y x) ∧ ∑' y, N y x ≤ B) →
    a' * (A * B) ≤ c ^ 2 * a →
    (∀ f, NormSummable w f →
      (∀ ι', ApplySummableAt T f ι') ∧ NormSummable w' (applyKernel T f)) ∧
    ∀ E : Set (Fin 3 × σ → ℂ), OpNormSummable w w' E (applyKernel T) ∧
      wOpNorm w w' E (applyKernel T) ≤ ENNReal.ofReal c
def Holds : Prop := ConstantWeights ∧ DiagonalInColour
end YangMills.Construction.PeriodicOperators.SchurTest
end
