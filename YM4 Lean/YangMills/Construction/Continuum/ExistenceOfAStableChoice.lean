import YangMills.Construction.Continuum.StableChoicesAndTheirFamilies
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.DisjointTuples
open TestFunctions
def SymmetricDenseChoiceExists : Prop :=
  ∀ L : ℕ, Odd L → 13 ≤ L → ∃ D : ratBoxUnions → Set RealFun, IsSymmetricDenseChoice L D
end YangMills.Construction.DisjointTuples
