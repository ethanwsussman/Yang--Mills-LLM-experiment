import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def relabelInvert {M M' : Type} (σ : M → M') (ε : M → ℤ) (X : M' → specialUnitary) :
    M → specialUnitary :=
  fun b => X (σ b) ^ ε b
def RelabelInvertPreservesHaar : Prop :=
  ∀ (M M' : Type) [Finite M] [Finite M'] (σ : M → M') (ε : M → ℤ),
    Function.Bijective σ → (∀ b, ε b = 1 ∨ ε b = -1) →
      IsHomeomorph (relabelInvert σ ε) ∧
      ∀ Φ : (M → specialUnitary) → ℂ, Measurable Φ → (∃ C : ℝ, ∀ Y, ‖Φ Y‖ ≤ C) →
        ∫ X, Φ (relabelInvert σ ε X) ∂haarPi M' = ∫ Y, Φ Y ∂haarPi M
end YangMills.Construction.Matrices.ComplexMatrix2
