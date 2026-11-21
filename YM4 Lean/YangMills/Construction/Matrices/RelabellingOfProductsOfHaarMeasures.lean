import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
open YangMills.Construction.Matrices.ComplexMatrix2
def relabel {Q A C : Type} (σ : Q ≃ A ⊕ A ⊕ C) (inv : Q → Bool)
    (y : (A → specialUnitary) × (A → specialUnitary) × (C → specialUnitary)) :
    Q → specialUnitary :=
  fun q => cond (inv q) (Sum.elim y.1 (Sum.elim y.2.1 y.2.2) (σ q))⁻¹
    (Sum.elim y.1 (Sum.elim y.2.1 y.2.2) (σ q))
def Statement : Prop :=
  ∀ (Q A C : Type) [Finite Q] [Finite A] [Finite C] (σ : Q ≃ A ⊕ A ⊕ C) (inv : Q → Bool),
    Measurable (relabel σ inv) ∧
      Measure.map (relabel σ inv)
        ((haarPi A).prod ((haarPi A).prod (haarPi C))) = haarPi Q
end YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
end
