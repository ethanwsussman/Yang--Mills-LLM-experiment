import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices (ComplexMatrix2)
namespace Tower.UnitScale.OneStep
section Statements
def DependsOnlyOn {ι κ : Type*} (D : Set (ι → ComplexMatrix2)) (S : Set ι)
    (f : (ι → ComplexMatrix2) → κ) : Prop :=
  ∀ a ∈ D, ∀ a' ∈ D, EqOn a a' S → f a = f a'
end Statements
end Tower.UnitScale.OneStep
end YangMills.Construction
end
