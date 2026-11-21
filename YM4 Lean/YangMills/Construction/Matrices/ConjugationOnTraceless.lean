import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Matrices.ComplexMatrix2
def ConjugationPreservesTraceless : Prop :=
  (∀ g ∈ unitDeterminant, IsUnit g) ∧
  (∀ g ∈ (specialUnitary : Set ComplexMatrix2), IsUnit g) ∧
  ∀ g : ComplexMatrix2, IsUnit g →
    (∀ X : ComplexMatrix2, conjugateBy g X = g * X * g⁻¹) ∧
    (∀ X : ComplexMatrix2, fullTrace (g * X * g⁻¹) = fullTrace X) ∧
    (∀ X : ComplexMatrix2, fullTrace X = 0 → fullTrace (conjugateBy g X) = 0) ∧
    Set.MapsTo (conjugateBy g) (traceless : Set ComplexMatrix2) (traceless : Set ComplexMatrix2) ∧
    (∀ (a b : ℂ), ∀ X ∈ traceless, ∀ X' ∈ traceless,
      conjugateBy g (a • X + b • X') = a • conjugateBy g X + b • conjugateBy g X') ∧
    Set.SurjOn (conjugateBy g) (traceless : Set ComplexMatrix2) (traceless : Set ComplexMatrix2) ∧
    Set.InjOn (conjugateBy g) (traceless : Set ComplexMatrix2) ∧
    ∀ X ∈ traceless, conjugateBy g⁻¹ (conjugateBy g X) = X ∧ X = conjugateBy g (conjugateBy g⁻¹ X)
end YangMills.Construction.Matrices.ComplexMatrix2
