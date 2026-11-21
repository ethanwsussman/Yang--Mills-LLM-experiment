import YangMills.Construction.Lattice.AverageTermOnACubeProof
import YangMills.Construction.Lattice.LiftsOfTheTorusInEveryDimension
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace TorusLifts
open ScaledFun
variable {d N : ℕ}
theorem norm_coe_le_abs (hN : 0 < N) (x : ℝ) : ‖(x : AddCircle (N : ℝ))‖ ≤ |x| := by apply _root_.YangMills.SharedProofs.p53979 <;> assumption
def backwardDiff (s : Mesh N) (μ : Fin d) : SiteFun d s →ₗ[ℝ] SiteFun d s where
  toFun f := ofMap fun x => s.h⁻¹ * (f (x - s.basisStep μ) - f x)
  map_add' f g := ScaledFun.ext fun x => by
    simp only [ofMap_apply, add_apply]; ring
  map_smul' c f := ScaledFun.ext fun x => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply]; ring
theorem adjoint_forwardDiff (s : Mesh N) (μ : Fin d) :
    LinearMap.adjoint (forwardDiff s μ) = backwardDiff s μ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro f g
  rw [ScaledFun.inner_eq, ScaledFun.inner_eq]
  have shift : ∑ x, s.h ^ d * f (x - s.basisStep μ) * g x =
      ∑ x, s.h ^ d * f x * g (x + s.basisStep μ) :=
    Fintype.sum_equiv (Equiv.subRight (s.basisStep μ)) _ _ fun x => by simp
  have e1 : ∑ x, s.h ^ d * backwardDiff s μ f x * g x =
      s.h⁻¹ * (∑ x, s.h ^ d * f (x - s.basisStep μ) * g x - ∑ x, s.h ^ d * f x * g x) := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    show s.h ^ d * (s.h⁻¹ * (f (x - s.basisStep μ) - f x)) * g x = _
    ring
  have e2 : ∑ x, s.h ^ d * f x * forwardDiff s μ g x =
      s.h⁻¹ * (∑ x, s.h ^ d * f x * g (x + s.basisStep μ) - ∑ x, s.h ^ d * f x * g x) := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    show s.h ^ d * f x * (s.h⁻¹ * (g (x + s.basisStep μ) - g x)) = _
    ring
  rw [e1, e2, shift]
variable {L j : ℕ}
theorem two_le_period (S : Scales d L j N) : 2 ≤ N := by
  obtain ⟨k, hk, hN⟩ := S.even_multiple
  have h : 0 < k * L := Nat.mul_pos hk S.factor_pos
  rw [hN, mul_assoc]
  omega
end TorusLifts
end YangMills.Construction.PeriodicLattice
