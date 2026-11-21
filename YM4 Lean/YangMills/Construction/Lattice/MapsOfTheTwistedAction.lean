import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def conjugationLinearMap (V : ComplexMatrix2) :
    ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless where
  toFun A := ⟨ComplexMatrix2.conjugateBy V A, by
    have hA : Matrix.trace (A : ComplexMatrix2) = 0 := A.2
    show Matrix.trace (V * (A : ComplexMatrix2) * V⁻¹) = 0
    by_cases h : IsUnit V.det
    · rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul V h, one_mul, hA]
    · rw [Matrix.nonsing_inv_apply_not_isUnit V h]
      simp⟩
  map_add' A B := by
    apply Subtype.ext
    simp only [ComplexMatrix2.conjugateBy, Submodule.coe_add, mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    simp [ComplexMatrix2.conjugateBy]
def twistedLinkMap (σ : FourTorus L m ≃ FourTorus L m) (V₀ : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) : ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless :=
  open Classical in
  if (bondImage σ b).IsPositivelyOriented then LinearMap.id
  else -conjugationLinearMap (V₀ b)⁻¹
end YangMills.Construction.PeriodicLattice
