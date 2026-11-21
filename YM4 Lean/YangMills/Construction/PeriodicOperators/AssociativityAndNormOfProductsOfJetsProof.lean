import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.AssociativityAndNormOfProductsOfJets
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetProducts
open JetQuad
variable {P₁ P₂ P₃ P₄ : PeriodicData}
theorem mul_assoc_eqAsJet (δ : ℝ) (p : Fin 4 → ℂ) (A : JetQuad P₂ P₁) (B : JetQuad P₃ P₂)
    (C : JetQuad P₄ P₃) : EqAsJet δ p (mul p (mul p A B) C) (mul p A (mul p B C)) := by
  refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩ <;>
    simp only [mul, LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_assoc, sub_add_cancel,
      add_sub_cancel_right] <;>
    abel
theorem sum_four_le_mul_sum_four (a b c d a' b' c' d' y₁ y₂ y₃ y₄ : ℝ≥0∞) (h₁ : y₁ ≤ a * a')
    (h₂ : y₂ ≤ b * a' + a * b') (h₃ : y₃ ≤ c * a' + a * c')
    (h₄ : y₄ ≤ d * a' + a * d' + b * c' + c * b') :
    y₁ + y₂ + y₃ + y₄ ≤ (a + b + c + d) * (a' + b' + c' + d') := by
  calc y₁ + y₂ + y₃ + y₄
      ≤ a * a' + (b * a' + a * b') + (c * a' + a * c') +
          (d * a' + a * d' + b * c' + c * b') := by gcongr
    _ ≤ a * a' + (b * a' + a * b') + (c * a' + a * c') +
          (d * a' + a * d' + b * c' + c * b') +
          (b * b' + b * d' + c * c' + c * d' + d * b' + d * c' + d * d') := le_self_add
    _ = (a + b + c + d) * (a' + b' + c' + d') := by ring
theorem apply_le_biSup {D : Set (Fin 4 → ℂ)} (f : (Fin 4 → ℂ) → ℝ≥0∞) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ D) : f κ ≤ ⨆ κ ∈ D, f κ :=
  le_iSup₂ (f := fun κ (_ : κ ∈ D) => f κ) κ hκ
theorem jetNorm_mul_le {δ : ℝ} {p : Fin 4 → ℂ} (hnorm : QuotMatrixNorms.Claim)
    (harg : ProductJetArguments δ p) (h₁ : IsPeriodic P₁)
    (h₂ : IsPeriodic P₂) (h₃ : IsPeriodic P₃) (A : JetQuad P₂ P₁)
    (B : JetQuad P₃ P₂) : jetNorm δ p (mul p A B) ≤ jetNorm δ p A * jetNorm δ p B := by
  have hcomp : ∀ (M : QuotHom P₂ P₁) (N : QuotHom P₃ P₂),
      quotHomNorm (M.comp N) ≤ quotHomNorm M * quotHomNorm N :=
    (hnorm P₂ P₁ P₃ h₂ h₁ h₃).2.1
  have hsum : ∀ M N : QuotHom P₃ P₁,
      quotHomNorm (M + N) ≤ quotHomNorm M + quotHomNorm N :=
    (hnorm P₃ P₁ P₁ h₃ h₁ h₁).1.2.1
  have bound : ∀ {M : QuotHom P₂ P₁} {N : QuotHom P₃ P₂} {x y : ℝ≥0∞},
      quotHomNorm M ≤ x → quotHomNorm N ≤ y → quotHomNorm (M.comp N) ≤ x * y :=
    fun hx hy => (hcomp _ _).trans (mul_le_mul' hx hy)
  have A00 := fun {κ} =>
    apply_le_biSup (D := imStrip (2 * δ)) (fun κ => quotHomNorm (A.f00 κ)) (κ := κ)
  have A10 := fun {κ} =>
    apply_le_biSup (D := stripAddShift δ p) (fun κ => quotHomNorm (A.f10 κ)) (κ := κ)
  have A01 := fun {κ} =>
    apply_le_biSup (D := stripSubShift δ p) (fun κ => quotHomNorm (A.f01 κ)) (κ := κ)
  have A11 := fun {κ} =>
    apply_le_biSup (D := realDualPoints) (fun κ => quotHomNorm (A.f11 κ)) (κ := κ)
  have B00 := fun {κ} =>
    apply_le_biSup (D := imStrip (2 * δ)) (fun κ => quotHomNorm (B.f00 κ)) (κ := κ)
  have B10 := fun {κ} =>
    apply_le_biSup (D := stripAddShift δ p) (fun κ => quotHomNorm (B.f10 κ)) (κ := κ)
  have B01 := fun {κ} =>
    apply_le_biSup (D := stripSubShift δ p) (fun κ => quotHomNorm (B.f01 κ)) (κ := κ)
  have B11 := fun {κ} =>
    apply_le_biSup (D := realDualPoints) (fun κ => quotHomNorm (B.f11 κ)) (κ := κ)
  refine sum_four_le_mul_sum_four _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · exact iSup₂_le fun κ hκ => bound (A00 hκ) (B00 hκ)
  · refine iSup₂_le fun κ hκ => ?_
    obtain ⟨hA, hB, hA', hB'⟩ := harg.comp10 κ hκ
    exact (hsum _ _).trans (add_le_add (bound (A10 hA) (B00 hB)) (bound (A00 hA') (B10 hB')))
  · refine iSup₂_le fun κ hκ => ?_
    obtain ⟨hA, hB, hA', hB'⟩ := harg.comp01 κ hκ
    exact (hsum _ _).trans (add_le_add (bound (A01 hA) (B00 hB)) (bound (A00 hA') (B01 hB')))
  · refine iSup₂_le fun κ hκ => ?_
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := harg.comp11 κ hκ
    exact (hsum _ _).trans (add_le_add ((hsum _ _).trans (add_le_add
      ((hsum _ _).trans (add_le_add (bound (A11 e₁) (B00 e₂)) (bound (A00 e₃) (B11 e₄))))
      (bound (A10 e₅) (B01 e₆)))) (bound (A01 e₇) (B10 e₈)))
theorem assoc_and_norm_le (hnorm : QuotMatrixNorms.Claim)
    (harg : JetArgumentsAndEqualJets) : JetProductsAssocAndNormLe :=
  fun δ p hδ hp _ _ _ _ h₁ h₂ h₃ _ A B C _ _ _ =>
    ⟨mul_assoc_eqAsJet δ p A B C,
      jetNorm_mul_le hnorm (harg.1 δ p hδ hp).2.1 h₁ h₂ h₃ A B⟩
end YangMills.Construction.PeriodicOperators.JetProducts
end
