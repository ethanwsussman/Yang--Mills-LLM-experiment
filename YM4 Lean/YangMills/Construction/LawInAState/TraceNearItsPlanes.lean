import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TraceBounds
def TraceNearPlaneValues : Prop :=
  ∀ (X S : Type) (P : Finset X) (pl : X → Fin 4 × Fin 4) (Pl : Finset (Fin 4 × Fin 4))
    (Y Z : Finset S) (κ κ' : S → X → X → ℝ) (T : X → X → ℝ) (H : S → S → Fin 4 × Fin 4 → Fin 4 × Fin 4 → ℝ)
    (W : S → X → ℝ) (α β : S → ℝ) (e b e₁ g M : ℝ),
    0 ≤ e → 0 ≤ b → 0 ≤ e₁ → 0 ≤ g → 0 ≤ M → (∀ p ∈ P, pl p ∈ Pl) → (∀ y p, 1 ≤ W y p) →
    (∀ y ∈ Y, ∀ z ∈ Z, ∀ p ∈ P, ∀ p' ∈ P, |T p p' - H y z (pl p) (pl p')| ≤ e * (W y p * W z p')) →
    (∀ y ∈ Y, ∀ z ∈ Z, ∀ p ∈ P, ∀ p' ∈ P, |T p' p - H y z (pl p') (pl p)| ≤ e * (W y p * W z p')) →
    (∀ y ∈ Y, ∀ z ∈ Z, ∀ A B, |H y z A B| ≤ b) →
    (∀ y ∈ Y, ∑ p ∈ P, ∑ p' ∈ P, |κ y p p'| * (W y p * W y p') ≤ M) →
    (∀ z ∈ Z, ∑ p ∈ P, ∑ p' ∈ P, |κ' z p p'| * (W z p * W z p') ≤ M) →
    (∀ y ∈ Y, ∀ A ∈ Pl, ∀ B ∈ Pl, |∑ p ∈ P.filter (fun p => pl p = A), ∑ p' ∈ P.filter (fun p' => pl p' = B), κ y p p' -
      (if A = B then α y else 0)| ≤ e₁) →
    (∀ z ∈ Z, ∀ A ∈ Pl, ∀ B ∈ Pl, |∑ p ∈ P.filter (fun p => pl p = A), ∑ p' ∈ P.filter (fun p' => pl p' = B), κ' z p p' -
      (if A = B then β z else 0)| ≤ e₁) →
    (∀ y ∈ Y, |α y| ≤ g) → (∀ z ∈ Z, |β z| ≤ g) →
    |∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (∑ y ∈ Y, κ y p₁ p₂) * T p₂ p₃ * (∑ z ∈ Z, κ' z p₃ p₄) * T p₄ p₁ -
      ∑ y ∈ Y, ∑ z ∈ Z, α y * β z * ∑ A ∈ Pl, ∑ B ∈ Pl, H y z A B * H y z B A| ≤
    (Y.card : ℝ) * (Z.card : ℝ) * (e * (2 * b + e) * M ^ 2 + (Pl.card : ℝ) ^ 4 * (e₁ * (2 * g + e₁) * b ^ 2))
end YangMills.Construction.TraceBounds
end
