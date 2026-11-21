import YangMills.Construction.Towers.KernelDeterminedByABilinearForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (KernelMatrix applyKernel unitKernel HasFiniteSupport)
namespace PolarisedKernel
variable {N : Type}
def basisFunction (ι : N) : N → ℂ := fun κ => unitKernel N κ ι
theorem basisFunction_self (ι : N) : basisFunction ι ι = 1 := by
  simp [basisFunction, unitKernel]
theorem basisFunction_of_ne {ι κ : N} (h : κ ≠ ι) : basisFunction ι κ = 0 := by
  simp [basisFunction, unitKernel, h]
theorem basisFunction_hasFiniteSupport (ι : N) : HasFiniteSupport (basisFunction ι) := by
  show (Function.support (basisFunction ι)).Finite
  refine (Set.finite_singleton ι).subset fun κ hκ => ?_
  by_contra h
  exact hκ (basisFunction_of_ne (by simpa using h))
theorem hasSum_mul_basisFunction (F : N → ℂ) (ι : N) :
    HasSum (fun κ => F κ * basisFunction ι κ) (F ι) := by
  have h := hasSum_single (f := fun κ => F κ * basisFunction ι κ) ι
    (fun κ hκ => by simp [basisFunction_of_ne hκ])
  simpa [basisFunction_self] using h
theorem applyKernel_basisFunction (T : KernelMatrix N N) (ι κ : N) :
    applyKernel T (basisFunction ι) κ = T κ ι :=
  (hasSum_mul_basisFunction (T κ) ι).tsum_eq
theorem applyKernel_add_basisFunction (T : KernelMatrix N N) (ι ι' κ : N) :
    applyKernel T (basisFunction ι + basisFunction ι') κ = T κ ι + T κ ι' := by
  have h := ((hasSum_mul_basisFunction (T κ) ι).add (hasSum_mul_basisFunction (T κ) ι')).tsum_eq
  rw [← h]
  exact tsum_congr fun j => by simp [mul_add]
theorem wPairing_basisFunction (w : ℝ) (ι : N) (h : N → ℂ) :
    PeriodicOperators.wPairing (fun _ : N => w) (basisFunction ι) h = (w : ℂ) * h ι := by
  have hs := ((hasSum_mul_basisFunction h ι).mul_left (w : ℂ)).tsum_eq
  rw [← hs]
  exact tsum_congr fun j => by simp [mul_comm]
theorem wPairing_add_basisFunction (w : ℝ) (ι ι' : N) (h : N → ℂ) :
    PeriodicOperators.wPairing (fun _ : N => w) (basisFunction ι + basisFunction ι') h =
      (w : ℂ) * (h ι + h ι') := by
  have hs := (((hasSum_mul_basisFunction h ι).add
    (hasSum_mul_basisFunction h ι')).mul_left (w : ℂ)).tsum_eq
  rw [← hs]
  refine tsum_congr fun j => ?_
  simp only [Pi.add_apply]
  ring
theorem valueAtUnits_holds : ValueAtUnits := by
  intro N T w β _ hsym hβ hform ι ι'
  change β (basisFunction ι) (basisFunction ι') = (w : ℂ) * T ι ι'
  have hf := basisFunction_hasFiniteSupport ι
  have hg := basisFunction_hasFiniteSupport ι'
  have hfg : HasFiniteSupport (basisFunction ι + basisFunction ι') :=
    (Set.Finite.union hf hg).subset (Function.support_add _ _)
  have hff : β (basisFunction ι) (basisFunction ι) = (w : ℂ) * T ι ι := by
    rw [hform _ hf, wPairing_basisFunction, applyKernel_basisFunction]
  have hgg : β (basisFunction ι') (basisFunction ι') = (w : ℂ) * T ι' ι' := by
    rw [hform _ hg, wPairing_basisFunction, applyKernel_basisFunction]
  have hsum : β (basisFunction ι + basisFunction ι') (basisFunction ι + basisFunction ι') =
      (w : ℂ) * ((T ι ι + T ι ι') + (T ι' ι + T ι' ι')) := by
    rw [hform _ hfg, wPairing_add_basisFunction, applyKernel_add_basisFunction,
      applyKernel_add_basisFunction]
  have hadd : ∀ h : N → ℂ, HasFiniteSupport h →
      β (basisFunction ι + basisFunction ι') h = β (basisFunction ι) h + β (basisFunction ι') h := by
    intro h hh
    simpa using hβ.add_smul_left 1 (basisFunction ι) (basisFunction ι') h hf hg hh
  have hexp : β (basisFunction ι + basisFunction ι') (basisFunction ι + basisFunction ι') =
      β (basisFunction ι) (basisFunction ι) + β (basisFunction ι') (basisFunction ι') +
        2 * β (basisFunction ι) (basisFunction ι') := by
    rw [hadd _ hfg, hβ.symm _ _ hf hfg, hβ.symm _ _ hg hfg, hadd _ hf, hadd _ hg,
      hβ.symm _ _ hg hf]
    ring
  have hs := hsym ι ι'
  linear_combination (1 / 2) * hsum - (1 / 2) * hexp - (1 / 2) * hff - (1 / 2) * hgg -
    ((w : ℂ) / 2) * hs
end PolarisedKernel
end YangMills.Construction.Tower
end
