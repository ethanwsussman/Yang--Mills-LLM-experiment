import YangMills.Construction.PositiveDefinite.KernelSesquilinearForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.PositiveDefinite.KernelSesqForm
variable {X : Type}
theorem kernelSesqForm_eq_finset_sum (k : X → X → ℂ) (φ ψ : X →₀ ℂ) {s t : Finset X}
    (hs : φ.support ⊆ s) (ht : ψ.support ⊆ t) :
    kernelSesqForm k φ ψ = ∑ x ∈ s, ∑ y ∈ t, conj (φ x) * ψ y * k x y := by
  unfold kernelSesqForm
  rw [Finset.sum_subset hs]
  · refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_subset ht fun y _ hy => ?_
    simp [Finsupp.notMem_support_iff.mp hy]
  · intro x _ hx
    simp [Finsupp.notMem_support_iff.mp hx]
theorem kernelSesqForm_add_right (k : X → X → ℂ) (φ ψ ψ' : X →₀ ℂ) :
    kernelSesqForm k φ (ψ + ψ') = kernelSesqForm k φ ψ + kernelSesqForm k φ ψ' := by
  classical
  rw [kernelSesqForm_eq_finset_sum k φ (ψ + ψ') subset_rfl Finsupp.support_add,
    kernelSesqForm_eq_finset_sum k φ ψ subset_rfl (Finset.subset_union_left (s₂ := ψ'.support)),
    kernelSesqForm_eq_finset_sum k φ ψ' subset_rfl (Finset.subset_union_right (s₁ := ψ.support))]
  simp only [Finsupp.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
theorem kernelSesqForm_smul_right (k : X → X → ℂ) (a : ℂ) (φ ψ : X →₀ ℂ) :
    kernelSesqForm k φ (a • ψ) = a * kernelSesqForm k φ ψ := by
  classical
  rw [kernelSesqForm_eq_finset_sum k φ (a • ψ) subset_rfl Finsupp.support_smul,
    kernelSesqForm_eq_finset_sum k φ ψ subset_rfl subset_rfl]
  simp only [Finset.mul_sum, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring
theorem kernelSesqForm_add_left (k : X → X → ℂ) (φ ψ ψ' : X →₀ ℂ) :
    kernelSesqForm k (ψ + ψ') φ = kernelSesqForm k ψ φ + kernelSesqForm k ψ' φ := by
  classical
  rw [kernelSesqForm_eq_finset_sum k (ψ + ψ') φ Finsupp.support_add subset_rfl,
    kernelSesqForm_eq_finset_sum k ψ φ (Finset.subset_union_left (s₂ := ψ'.support)) subset_rfl,
    kernelSesqForm_eq_finset_sum k ψ' φ (Finset.subset_union_right (s₁ := ψ.support)) subset_rfl]
  simp only [Finsupp.add_apply, map_add, add_mul, Finset.sum_add_distrib]
theorem kernelSesqForm_smul_left (k : X → X → ℂ) (a : ℂ) (φ ψ : X →₀ ℂ) :
    kernelSesqForm k (a • ψ) φ = conj a * kernelSesqForm k ψ φ := by
  classical
  rw [kernelSesqForm_eq_finset_sum k (a • ψ) φ Finsupp.support_smul subset_rfl,
    kernelSesqForm_eq_finset_sum k ψ φ subset_rfl subset_rfl]
  simp only [Finset.mul_sum, Finsupp.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring
theorem KernelPosSemidef.finset_double_sum_nonneg {k : X → X → ℂ} (hk : KernelPosSemidef k)
    (s : Finset X) (a : X → ℂ) : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, conj (a x) * a y * k x y := by
  have hre : ∀ G : X → ℂ, ∑ i, G (s.equivFin.symm i) = ∑ x ∈ s, G x := by
    intro G
    rw [Equiv.sum_comp s.equivFin.symm (fun z : s => G z)]
    exact Finset.sum_coe_sort s G
  have hpos := hk s.card (fun i => (s.equivFin.symm i : X)) (fun i => a (s.equivFin.symm i))
  have heq : (∑ i, ∑ j, conj (a (s.equivFin.symm i)) * a (s.equivFin.symm j) *
        k (s.equivFin.symm i) (s.equivFin.symm j)) =
      ∑ x ∈ s, ∑ y ∈ s, conj (a x) * a y * k x y := by
    rw [← hre (fun x => ∑ y ∈ s, conj (a x) * a y * k x y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hre (fun y => conj (a (s.equivFin.symm i)) * a y * k (s.equivFin.symm i) y)
  exact hpos.trans_eq heq
theorem kernelSesqForm_self_nonneg {k : X → X → ℂ} (hk : KernelPosSemidef k) (φ : X →₀ ℂ) :
    0 ≤ kernelSesqForm k φ φ :=
  KernelPosSemidef.finset_double_sum_nonneg hk φ.support φ
theorem kernelSesqForm_conj_symm {k : X → X → ℂ} (hk : KernelPosSemidef k) (φ ψ : X →₀ ℂ) :
    kernelSesqForm k ψ φ = conj (kernelSesqForm k φ ψ) := by
  have h₁ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk φ)).2
  have h₂ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk ψ)).2
  have h₃ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk (φ + ψ))).2
  have h₄ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk (φ + Complex.I • ψ))).2
  have e₃ : kernelSesqForm k (φ + ψ) (φ + ψ) = kernelSesqForm k φ φ + kernelSesqForm k φ ψ +
      (kernelSesqForm k ψ φ + kernelSesqForm k ψ ψ) := by
    rw [kernelSesqForm_add_left, kernelSesqForm_add_right, kernelSesqForm_add_right]
  have e₄ : kernelSesqForm k (φ + Complex.I • ψ) (φ + Complex.I • ψ) =
      kernelSesqForm k φ φ + Complex.I * kernelSesqForm k φ ψ -
        Complex.I * kernelSesqForm k ψ φ + kernelSesqForm k ψ ψ := by
    rw [kernelSesqForm_add_left, kernelSesqForm_add_right, kernelSesqForm_add_right,
      kernelSesqForm_smul_right, kernelSesqForm_smul_left, kernelSesqForm_smul_left,
      kernelSesqForm_smul_right, Complex.conj_I]
    have hI : -Complex.I * (Complex.I * kernelSesqForm k ψ ψ) = kernelSesqForm k ψ ψ := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [hI]
    ring
  rw [e₃] at h₃
  rw [e₄] at h₄
  simp only [Complex.zero_im, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at h₁ h₂ h₃ h₄
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
theorem kernelSesqForm_norm_sq_le {k : X → X → ℂ} (hk : KernelPosSemidef k) (φ ψ : X →₀ ℂ) :
    ‖kernelSesqForm k φ ψ‖ ^ 2 ≤ (kernelSesqForm k φ φ).re * (kernelSesqForm k ψ ψ).re := by
  let core : PreInnerProductSpace.Core ℂ (X →₀ ℂ) :=
    { inner := kernelSesqForm k
      conj_inner_symm := fun x y => (kernelSesqForm_conj_symm hk y x).symm
      re_inner_nonneg := fun x => (Complex.le_def.mp (kernelSesqForm_self_nonneg hk x)).1
      add_left := fun x y z => kernelSesqForm_add_left k z x y
      smul_left := fun x y r => kernelSesqForm_smul_left k r y x }
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) φ ψ
  change ‖kernelSesqForm k φ ψ‖ * ‖kernelSesqForm k ψ φ‖ ≤
    (kernelSesqForm k φ φ).re * (kernelSesqForm k ψ ψ).re at h
  rw [kernelSesqForm_conj_symm hk φ ψ, Complex.norm_conj] at h
  rw [pow_two]
  exact h
theorem kernelSesqForm_cauchy_schwarz {k : X → X → ℂ} (hk : KernelPosSemidef k)
    (φ ψ : X →₀ ℂ) :
    ((‖kernelSesqForm k φ ψ‖ ^ 2 : ℝ) : ℂ) ≤ kernelSesqForm k φ φ * kernelSesqForm k ψ ψ := by
  have h₁ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk φ)).2
  have h₂ := (Complex.le_def.mp (kernelSesqForm_self_nonneg hk ψ)).2
  have e : kernelSesqForm k φ φ * kernelSesqForm k ψ ψ =
      (((kernelSesqForm k φ φ).re * (kernelSesqForm k ψ ψ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, ← h₁, ← h₂, Complex.zero_im, mul_zero,
        sub_zero]
    · simp only [Complex.mul_im, Complex.ofReal_im, ← h₁, ← h₂, Complex.zero_im, mul_zero,
        zero_mul, add_zero]
  rw [e]
  exact Complex.real_le_real.mpr (kernelSesqForm_norm_sq_le hk φ ψ)
theorem kernelSesqForm_single_single (k : X → X → ℂ) (x y : X) :
    kernelSesqForm k (Finsupp.single x 1) (Finsupp.single y 1) = k x y := by
  rw [kernelSesqForm_eq_finset_sum k _ _ (s := {x}) (t := {y}) Finsupp.support_single_subset
    Finsupp.support_single_subset]
  simp
theorem sesqFormProperties_holds : SesqFormProperties := by
  intro X k hk
  refine ⟨⟨kernelSesqForm_add_right k, kernelSesqForm_smul_right k,
    fun φ ψ ψ' => kernelSesqForm_add_left k φ ψ ψ', kernelSesqForm_smul_left k, ?_⟩, ?_⟩
  · exact fun φ ψ => ⟨kernelSesqForm_self_nonneg hk φ, kernelSesqForm_conj_symm hk φ ψ,
      kernelSesqForm_cauchy_schwarz hk φ ψ⟩
  · intro x y
    have h₁ := kernelSesqForm_self_nonneg hk (Finsupp.single x 1)
    have h₂ := kernelSesqForm_conj_symm hk (Finsupp.single x 1) (Finsupp.single y 1)
    have h₃ := kernelSesqForm_cauchy_schwarz hk (Finsupp.single x 1) (Finsupp.single y 1)
    simp only [kernelSesqForm_single_single] at h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
end YangMills.Construction.PositiveDefinite.KernelSesqForm
