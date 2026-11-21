import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
def HolomorphyClosureStatement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (U : Set (ι ⊕ κ → ComplexMatrix2)), ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) U →
    (∀ M : ComplexMatrix2, IsHolomorphicToMatrixEntries b U fun _ => M) ∧
    (∀ x : ι ⊕ κ, IsHolomorphicToMatrixEntries b U fun q => q x) ∧
    (∀ F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      IsHolomorphicToMatrixEntries b U G → IsHolomorphicToMatrixEntries b U fun q => F q + G q) ∧
    (∀ F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      IsHolomorphicToMatrixEntries b U G → IsHolomorphicToMatrixEntries b U fun q => F q * G q) ∧
    (∀ (L : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2) (F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicToMatrixEntries b U F →
      IsHolomorphicToMatrixEntries b U fun q => L (F q)) ∧
    (∀ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      (∀ q ∈ U, IsUnit (F q).det) → IsHolomorphicToMatrixEntries b U fun q => (F q)⁻¹) ∧
    (∀ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      IsHolomorphicToMatrixEntries b U fun q => ComplexMatrix2.matExp (F q)) ∧
    (∀ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      MapsTo F U ComplexMatrix2.logBall →
      IsHolomorphicToMatrixEntries b U fun q => ComplexMatrix2.logSeries (F q)) ∧
    (∀ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      ∀ O : Set ComplexMatrix2, IsOpen O →
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (U ∩ F ⁻¹' O)) ∧
    (∀ U' ⊆ U, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) U' →
      ∀ F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
        IsHolomorphicToMatrixEntries b U' F) ∧
    (∀ F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2, IsHolomorphicToMatrixEntries b U F →
      EqOn G F U → IsHolomorphicToMatrixEntries b U G)
end YangMills.Construction.Matrices.GroupLieProduct
