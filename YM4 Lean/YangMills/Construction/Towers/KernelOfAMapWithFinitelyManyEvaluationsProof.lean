import YangMills.Construction.Towers.KernelDeterminedByABilinearFormProof
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FiniteSupportKernel
open YangMills.Construction.PeriodicOperators
theorem basisFunction_self {N : Type} (ι : N) : (basisFunction ι : N → ℂ) ι = 1 := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_self <;> assumption
theorem basisFunction_of_ne {N : Type} {ι κ : N} (h : κ ≠ ι) :
    (basisFunction ι : N → ℂ) κ = 0 := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_of_ne <;> assumption
theorem additive_map_finset_sum {N N' : Type} {M : (N → ℂ) → N' → ℂ}
    (hadd : ∀ f g, M (f + g) = M f + M g) (hzero : M 0 = 0) {X : Type} (A : Finset X)
    (u : X → N → ℂ) : M (∑ x ∈ A, u x) = ∑ x ∈ A, M (u x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using hzero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
theorem sum_smul_basisFunction_apply {N : Type} (A : Finset N) (f : N → ℂ) {κ : N}
    (hκ : κ ∈ A) : (∑ ι ∈ A, f ι • (basisFunction ι : N → ℂ)) κ = f κ := by
  rw [Finset.sum_apply, Finset.sum_eq_single κ]
  · simp [basisFunction_self]
  · intro ι _ h
    simp [basisFunction_of_ne h.symm]
  · exact fun h => absurd hκ h
theorem kernelOfFiniteSupportMap_holds : KernelOfFiniteSupportMap := by
  intro N N' M hadd hsmul hread
  have hzero : M 0 = 0 := by simpa using hsmul 0 0
  have hrow : ∀ (ι' : N') (A : Finset N),
      (∀ f g : N → ℂ, (∀ ι ∈ A, f ι = g ι) → M f ι' = M g ι') →
      ∀ ι, ι ∉ A → M (basisFunction ι : N → ℂ) ι' = 0 := by
    intro ι' A hA ι hι
    have e := hA (basisFunction ι : N → ℂ) 0 fun κ hκ =>
      basisFunction_of_ne fun h => hι (h ▸ hκ)
    rw [e, hzero]
    rfl
  have hvalue : ∀ (ι' : N') (A : Finset N),
      (∀ f g : N → ℂ, (∀ ι ∈ A, f ι = g ι) → M f ι' = M g ι') →
      ∀ f : N → ℂ, M f ι' = ∑ ι ∈ A, M (basisFunction ι : N → ℂ) ι' * f ι := by
    intro ι' A hA f
    have e := hA f (∑ ι ∈ A, f ι • (basisFunction ι : N → ℂ)) fun κ hκ =>
      (sum_smul_basisFunction_apply A f hκ).symm
    rw [e, additive_map_finset_sum hadd hzero, Finset.sum_apply]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [hsmul]
    simp [mul_comm]
  have hgiven : Represents (fun ι' ι => M (basisFunction ι : N → ℂ) ι') M := by
    intro f
    refine ⟨fun ι' => ?_, funext fun ι' => ?_⟩
    · obtain ⟨A, hA⟩ := hread ι'
      refine summable_of_ne_finset_zero (s := A) fun ι hι => ?_
      simp [hrow ι' A hA ι hι]
    · obtain ⟨A, hA⟩ := hread ι'
      show ∑' ι, M (basisFunction ι : N → ℂ) ι' * f ι = M f ι'
      rw [hvalue ι' A hA f]
      refine tsum_eq_sum fun ι hι => ?_
      simp [hrow ι' A hA ι hι]
  refine ⟨hgiven, ?_⟩
  have hs : Represents (kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => Represents T M) ⟨_, hgiven⟩
  funext ι' ι
  have e := congrFun (hs (basisFunction ι : N → ℂ)).2 ι'
  rw [← e]
  show _ = ∑' κ, kernelOfMap M ι' κ * (basisFunction ι : N → ℂ) κ
  rw [tsum_eq_single ι fun κ h => by simp [basisFunction_of_ne h], basisFunction_self, mul_one]
end YangMills.Construction.Tower.FullSpace.FiniteSupportKernel
