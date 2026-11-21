import YangMills.Construction.PeriodicOperators.ProductsOfKernelsWithFiniteRows
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RowFiniteKernels
variable {N₀ N₁ N₂ : Type}
theorem summable_norm_of_support_finite {α : Type} {F : α → ℂ} (h : (Function.support F).Finite) :
    Summable fun a => ‖F a‖ :=
  summable_of_hasFiniteSupport (h.subset fun a ha => by
    simpa [Function.mem_support] using ha)
theorem applySummable_of_rowFinite {S : KernelMatrix N₂ N₁} (hS : RowFinite S) (f : N₂ → ℂ) :
    ApplySummable S f := fun i =>
  summable_norm_of_support_finite ((hS i).subset fun j hj h0 => hj (by simp [h0]))
theorem applyKernel_eq_finset_sum {S : KernelMatrix N₂ N₁} (f : N₂ → ℂ) (i : N₁) (B : Finset N₂)
    (hB : ∀ j, j ∉ B → S i j = 0) :
    applyKernel S f i = ∑ j ∈ B, S i j * f j :=
  tsum_eq_sum fun j hj => by simp [hB j hj]
theorem compKernel_eq_finset_sum {T : KernelMatrix N₁ N₀} {S : KernelMatrix N₂ N₁} (a : N₀) (c : N₂)
    (A : Finset N₁) (hA : ∀ j, j ∉ A → T a j = 0) :
    compKernel T S a c = ∑ j ∈ A, T a j * S j c :=
  tsum_eq_sum fun j hj => by simp [hA j hj]
theorem applyComp_holds : ApplyComp := by
  classical
  intro N₁ N₂ S hS
  refine ⟨applySummable_of_rowFinite hS, fun N₀ T hT => ?_⟩
  let A : N₀ → Finset N₁ := fun a => (hT a).toFinset
  let B : N₀ → Finset N₂ := fun a => (A a).biUnion fun b => (hS b).toFinset
  have hA : ∀ a j, j ∉ A a → T a j = 0 := fun a j hj => by
    simpa [A] using hj
  have hB : ∀ a b c, b ∈ A a → c ∉ B a → S b c = 0 := fun a b c hb hc => by
    by_contra h
    exact hc (Finset.mem_biUnion.2 ⟨b, hb, by simpa using h⟩)
  have hrows : RowFinite (compKernel T S) := fun a =>
    (B a).finite_toSet.subset fun c hc => by
      by_contra h
      refine hc ?_
      rw [compKernel_eq_finset_sum a c (A a) (hA a)]
      exact Finset.sum_eq_zero fun b hb => by simp [hB a b c hb h]
  have hsum : CompSummable T S := fun a c =>
    summable_norm_of_support_finite ((hT a).subset fun j hj h0 => hj (by simp [h0]))
  refine ⟨hsum, hrows, fun f => ⟨applySummable_of_rowFinite hrows f,
    applySummable_of_rowFinite hT _, ?_⟩⟩
  funext a
  rw [applyKernel_eq_finset_sum f a (B a) (fun c h => by
      rw [compKernel_eq_finset_sum a c (A a) (hA a)]
      exact Finset.sum_eq_zero fun b hb => by simp [hB a b c hb h]),
    applyKernel_eq_finset_sum (applyKernel S f) a (A a) (hA a)]
  have hleft : ∀ c, compKernel T S a c * f c = ∑ b ∈ A a, T a b * S b c * f c :=
    fun c => by rw [compKernel_eq_finset_sum a c (A a) (hA a), Finset.sum_mul]
  have hright : ∀ b ∈ A a, T a b * applyKernel S f b =
      ∑ c ∈ B a, T a b * S b c * f c := fun b hb => by
    rw [applyKernel_eq_finset_sum f b (B a) (fun c h => hB a b c hb h), Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (mul_assoc _ _ _).symm
  rw [Finset.sum_congr rfl fun c _ => hleft c, Finset.sum_congr rfl hright, Finset.sum_comm]
theorem compAssoc_holds : CompAssoc := by
  intro N₀ N₁ N₂ N₃ T S R hT hS
  obtain ⟨hSf, hTS⟩ := applyComp_holds N₁ N₂ S hS
  obtain ⟨-, -, hf⟩ := hTS N₀ T hT
  refine ⟨fun b d => hSf (fun c => R c d) b,
    fun a d => (hf fun c => R c d).1 a,
    fun a d => (hf fun c => R c d).2.1 a, ?_⟩
  funext a d
  exact congrFun (hf fun c => R c d).2.2 a
theorem unitLaws_holds : UnitLaws := by
  classical
  intro N₁
  have hzero : ∀ i j : N₁, i ≠ j → unitKernel N₁ i j = 0 := fun i j h => by
    simp [unitKernel, h]
  have hone : ∀ i : N₁, unitKernel N₁ i i = 1 := fun i => by simp [unitKernel]
  refine ⟨fun b => (finite_singleton b).subset fun j hj => ?_, fun N₀ T => ⟨fun a b => ?_, ?_⟩,
    fun N₂ S => ⟨fun b c => ?_, ?_⟩⟩
  · by_contra h
    exact hj (hzero _ _ fun e => h (by simp [e]))
  · refine summable_norm_of_support_finite ((finite_singleton b).subset fun j hj => ?_)
    by_contra h
    exact hj (by simp [hzero j b h])
  · funext a b
    refine (tsum_eq_single b fun j h => by simp [hzero j b h]).trans (by simp [hone])
  · refine summable_norm_of_support_finite ((finite_singleton b).subset fun j hj => ?_)
    by_contra h
    exact hj (by simp [hzero b j fun e => h (by simp [e])])
  · funext b c
    refine (tsum_eq_single b fun j h => by simp [hzero b j h.symm]).trans (by simp [hone])
theorem transposeDuality_holds : TransposeDuality := by
  classical
  intro N₀ N₁ T u v hT _ hv g hg f
  have hg' : (Function.support g).Finite := hg
  let A : Finset N₀ := hg'.toFinset
  let B : Finset N₁ := A.biUnion fun a => (hT a).toFinset
  have hA : ∀ j, j ∉ A → g j = 0 := fun j hj => by
    by_contra h
    exact hj (hg'.mem_toFinset.2 h)
  have hB : ∀ a b, a ∈ A → b ∉ B → T a b = 0 := fun a b ha hb => by
    by_contra h
    exact hb (Finset.mem_biUnion.2 ⟨a, ha, by simpa using h⟩)
  have happ : ∀ b, applyKernel (wTranspose v u T) g b =
      ∑ a ∈ A, wTranspose v u T b a * g a := fun b =>
    tsum_eq_sum fun j hj => by simp [hA j hj]
  have hzero : ∀ b, b ∉ B → applyKernel (wTranspose v u T) g b = 0 := fun b h => by
    rw [happ]
    exact Finset.sum_eq_zero fun a ha => by simp [wTranspose, hB a b ha h]
  have hsupp₁ : Function.support
      (fun b => (v b : ℂ) * (applyKernel (wTranspose v u T) g b * f b)) ⊆ (B : Set N₁) :=
    fun b hb => by
      by_contra h
      exact hb (by simp [hzero b h])
  have hsupp₀ : Function.support
      (fun a => (u a : ℂ) * (g a * applyKernel T f a)) ⊆ (A : Set N₀) :=
    fun a ha => by
      by_contra h
      exact ha (by simp [hA a h])
  refine ⟨applySummable_of_rowFinite hT f, fun b => ?_,
    B.finite_toSet.subset fun b hb => ?_, B.finite_toSet.subset hsupp₁,
    A.finite_toSet.subset hsupp₀, ?_⟩
  · refine summable_norm_of_support_finite (hg.subset fun j hj h0 => hj (by simp [h0]))
  · by_contra h
    exact hb (hzero b h)
  · rw [finsum_eq_sum_of_support_subset _ hsupp₁, finsum_eq_sum_of_support_subset _ hsupp₀]
    have hleft : ∀ b ∈ B, (v b : ℂ) * (applyKernel (wTranspose v u T) g b * f b) =
        ∑ a ∈ A, (u a : ℂ) * (g a * (T a b * f b)) := fun b _ => by
      have hne : (v b : ℂ) ≠ 0 := by exact_mod_cast (hv b).ne'
      rw [happ, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [wTranspose]
      push_cast
      field_simp
    have hright : ∀ a ∈ A, (u a : ℂ) * (g a * applyKernel T f a) =
        ∑ b ∈ B, (u a : ℂ) * (g a * (T a b * f b)) := fun a ha => by
      rw [applyKernel_eq_finset_sum f a B (fun b h => hB a b ha h), Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright, Finset.sum_comm]
theorem claim_holds : Claim :=
  ⟨applyComp_holds, compAssoc_holds, unitLaws_holds, transposeDuality_holds⟩
end YangMills.Construction.PeriodicOperators.RowFiniteKernels
end
