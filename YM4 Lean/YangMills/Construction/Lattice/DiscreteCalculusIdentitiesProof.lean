import YangMills.Construction.Lattice.DirectionalAverageLiftProof
import YangMills.Construction.Lattice.PoissonEstimatesOnTheTorusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DiscreteCalculus
open ScaledFun
variable {d N : ℕ} {s : Mesh N} {ι : Type}
theorem forwardDiff_apply (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s) :
    forwardDiff s μ f x = s.h⁻¹ * (f (x + s.basisStep μ) - f x) := rfl
def backwardDiff (s : Mesh N) (μ : Fin d) : SiteFun d s →ₗ[ℝ] SiteFun d s where
  toFun f := ofMap fun x => s.h⁻¹ * (f (x - s.basisStep μ) - f x)
  map_add' f g := ScaledFun.ext fun x => by
    simp only [ofMap_apply, add_apply]; ring
  map_smul' c f := ScaledFun.ext fun x => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply]; ring
theorem backwardDiff_apply (μ : Fin d) (f : SiteFun d s) (x : GridPoint d s) :
    backwardDiff s μ f x = s.h⁻¹ * (f (x - s.basisStep μ) - f x) := rfl
theorem sum_mul_shift (v : GridPoint d s) (f g : SiteFun d s) :
    ∑ x, s.h ^ d * f (x - v) * g x = ∑ x, s.h ^ d * f x * g (x + v) :=
  Fintype.sum_equiv (Equiv.subRight v) _ _ fun x => by simp
theorem adjoint_forwardDiff (μ : Fin d) :
    LinearMap.adjoint (forwardDiff s μ) = backwardDiff s μ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro f g
  rw [ScaledFun.inner_eq, ScaledFun.inner_eq]
  have e1 : ∑ x, s.h ^ d * backwardDiff s μ f x * g x =
      s.h⁻¹ * (∑ x, s.h ^ d * f (x - s.basisStep μ) * g x - ∑ x, s.h ^ d * f x * g x) := by
    rw [← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun x _ => by rw [backwardDiff_apply]; ring
  have e2 : ∑ x, s.h ^ d * f x * forwardDiff s μ g x =
      s.h⁻¹ * (∑ x, s.h ^ d * f x * g (x + s.basisStep μ) - ∑ x, s.h ^ d * f x * g x) := by
    rw [← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun x _ => by rw [forwardDiff_apply]; ring
  rw [e1, e2, sum_mul_shift]
end YangMills.Construction.PeriodicLattice.DiscreteCalculus
