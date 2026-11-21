import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def TranslatedDerivativeBound : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : BlockFrame) (j k : ℕ) (f : F.GaugeField j → imaginaryQuaternions) (W : F.GaugeField j)
    (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (c' : Fin k → F.Site j × Fin 4)
    (X' : Fin k → imaginaryQuaternions)
    (Bd : ∀ i : ℕ, (Fin i → F.Site j × Fin 4) → ℝ) (R : ℝ),
    k ≤ 2 → (∀ i, F.period j i ≠ 0) → ‖X‖ = 1 → AreUnitVectors X' → 0 ≤ R →
    (∀ (q : ℕ) (c'' : Fin q → F.Site j × Fin 4) (X'' : Fin q → imaginaryQuaternions),
      ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun τ : Fin q → ℝ => f (leftTranslate (bondSpread c'' X'' τ) W)) 0) →
    (∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4) (Xs : Fin i → imaginaryQuaternions), 1 ≤ i → i ≤ 3 →
      AreUnitVectors Xs → ‖bondDeriv f W bs Xs‖ ≤ Bd i bs) →
    (∀ (i : ℕ) (bs : Fin i → F.Site j × Fin 4), 1 ≤ i → i ≤ 3 →
      (∀ l : Fin (k + 1), ∃ m, (Fin.cons c c' : Fin (k + 1) → F.Site j × Fin 4) l = bs m) → Bd i bs ≤ R) →
    ContDiffAt ℝ (k : WithTop ℕ∞)
      (fun τ : Fin k → ℝ =>
        bondDeriv f (leftTranslate (bondSpread c' X' τ) W) (fun _ : Fin 1 => c) (fun _ => X)) 0 ∧
    ‖bondDeriv (fun W' => bondDeriv f W' (fun _ : Fin 1 => c) (fun _ => X)) W c' X'‖ ≤ M * R
end Estimates
end YangMills.Construction
end
