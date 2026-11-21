import YangMills.Construction.Dirichlet.FormsOperatorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeCalculus
namespace GroupSteps
variable {G : Type*} [AddCommGroup G] {d : ℕ}
def shiftSub (s : Fin d → G) (μ : Fin d) (f : G → ℝ) : G → ℝ := fun x => f (x - s μ)
def forwardDiff (ξ : ℝ) (s : Fin d → G) (μ : Fin d) (f : G → ℝ) : G → ℝ :=
  fun x => ξ⁻¹ * (f (x + s μ) - f x)
def backwardDiff (ξ : ℝ) (s : Fin d → G) (μ : Fin d) (f : G → ℝ) : G → ℝ :=
  fun x => ξ⁻¹ * (f (x - s μ) - f x)
def laplacian (ξ : ℝ) (s : Fin d → G) (f : G → ℝ) : G → ℝ :=
  fun x => ∑ μ, backwardDiff ξ s μ (forwardDiff ξ s μ f) x
theorem laplacian_eq {ξ : ℝ} (hξ : ξ ≠ 0) (s : Fin d → G) (f : G → ℝ) (x : G) :
    laplacian ξ s f x = (ξ ^ 2)⁻¹ * ∑ μ, ((f x - f (x + s μ)) + (f x - f (x - s μ))) := by
  simp only [laplacian, backwardDiff, forwardDiff, sub_add_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  field_simp
  ring
theorem summation_by_parts [Finite G] (ξ : ℝ) (s : Fin d → G) (g : G → ℝ) (F : Fin d → G → ℝ) :
    ξ ^ d * ∑ᶠ x, g x * ∑ μ, backwardDiff ξ s μ (F μ) x =
      ∑ μ, ξ ^ d * ∑ᶠ x, forwardDiff ξ s μ g x * F μ x := by
  classical
  have := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hshift : ∑ x, g x * (ξ⁻¹ * F μ (x - s μ)) = ∑ x, g (x + s μ) * (ξ⁻¹ * F μ x) := by
    refine Fintype.sum_equiv (Equiv.subRight (s μ)) _ _ fun x => ?_
    simp
  have hsplit : ∑ x, g x * (ξ⁻¹ * (F μ (x - s μ) - F μ x)) =
      ∑ x, g x * (ξ⁻¹ * F μ (x - s μ)) - ∑ x, g x * (ξ⁻¹ * F μ x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [backwardDiff, forwardDiff]
  rw [hsplit, hshift, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring
end GroupSteps
open GroupSteps
section Grid
variable {d : ℕ} {ξ : ℝ}
end Grid
section Block
variable {d : ℕ} {S ξ : ℝ}
end Block
end YangMills.Construction.LatticeCalculus
