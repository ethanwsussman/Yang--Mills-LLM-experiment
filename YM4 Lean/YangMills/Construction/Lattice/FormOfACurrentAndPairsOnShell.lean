import YangMills.Construction.Lattice.BareLatticeSpacesAndOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice Matrices
namespace PeriodicLattice.Bare
variable {L m : ℕ} {j : ℤ}
structure IsSymmetricRepresentative (X : Set (FourTorus L m)) (ξ : ℝ)
    (Q : (Bond L m j → ComplexMatrix2) → ℂ)
    (T : (Bond L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2) : Prop where
  map_mem : ∀ A ∈ bondFormSpace X, T A ∈ bondFormSpace X
  map_linear : ∀ A ∈ bondFormSpace X, ∀ B ∈ bondFormSpace X, ∀ c : ℂ, T (A + c • B) = T A + c • T B
  inner_symm : ∀ A ∈ bondFormSpace X, ∀ B ∈ bondFormSpace X,
    bondFormInnerOn X ξ A (T B) = bondFormInnerOn X ξ (T A) B
  inner_self_eq : ∀ A ∈ bondFormSpace X, bondFormInnerOn X ξ A (T A) = Q A
def symmetricRepresentative (X : Set (FourTorus L m)) (ξ : ℝ)
    (Q : (Bond L m j → ComplexMatrix2) → ℂ) :
    (Bond L m j → ComplexMatrix2) → Bond L m j → ComplexMatrix2 :=
  Classical.epsilon (IsSymmetricRepresentative X ξ Q)
end PeriodicLattice.Bare
end YangMills.Construction
end
