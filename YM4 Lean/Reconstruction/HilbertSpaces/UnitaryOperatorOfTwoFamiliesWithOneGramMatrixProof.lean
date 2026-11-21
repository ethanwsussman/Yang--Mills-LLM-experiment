import Reconstruction.HilbertSpaces.UnitaryOperatorOfTwoFamiliesWithOneGramMatrix
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.GramUnitary
theorem claim_holds : Claim := by
  intro H H' _ _ _ _ _ _ ι x y hxy hx hy
  let Lx := Finsupp.linearCombination ℂ x
  let Ly := Finsupp.linearCombination ℂ y
  have hinner : ∀ c d : ι →₀ ℂ, inner ℂ (Lx c) (Lx d) = inner ℂ (Ly c) (Ly d) := by
    intro c d
    simp only [Lx, Ly, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hxy]
  have hnorm : ∀ c : ι →₀ ℂ, ‖Lx c‖ = ‖Ly c‖ := by
    intro c
    have h : ‖Lx c‖ ^ 2 = ‖Ly c‖ ^ 2 := by
      have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (Lx c)
      have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (Ly c)
      rw [hinner c c, h2] at h1
      exact_mod_cast h1.symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have hker : LinearMap.ker Lx ≤ LinearMap.ker Ly := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, ← hnorm c, hc, norm_zero]
  let T₀ : LinearMap.range Lx →ₗ[ℂ] H' :=
    ((LinearMap.ker Lx).liftQ Ly hker).comp (Lx.quotKerEquivRange.symm : _ →ₗ[ℂ] _)
  have hT₀ : ∀ c : ι →₀ ℂ, T₀ ⟨Lx c, LinearMap.mem_range_self Lx c⟩ = Ly c := by
    intro c
    simp only [T₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  have hT₀norm : ∀ v : LinearMap.range Lx, ‖T₀ v‖ = ‖v‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hT₀ c, ← hnorm c]
    rfl
  have hrange : (LinearMap.range Lx : Set H) = Submodule.span ℂ (Set.range x) := by
    simp only [Lx, Finsupp.range_linearCombination]
  have hD : Dense (LinearMap.range Lx : Set H) := by rw [hrange]; exact hx
  have hdr : DenseRange ((LinearMap.range Lx).subtypeL : LinearMap.range Lx → H) :=
    hD.denseRange_val
  have hui : IsUniformInducing ((LinearMap.range Lx).subtypeL : LinearMap.range Lx → H) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  let S : LinearMap.range Lx →L[ℂ] H' :=
    T₀.mkContinuous 1 (fun v => by rw [hT₀norm v, one_mul])
  let T : H →L[ℂ] H' := S.extend (LinearMap.range Lx).subtypeL
  have hT : ∀ v : LinearMap.range Lx, T v = T₀ v := fun v =>
    ContinuousLinearMap.extend_eq S hdr hui v
  have hTnorm : ∀ ξ : H, ‖T ξ‖ = ‖ξ‖ := by
    intro ξ
    have hclosed : IsClosed {ξ : H | ‖T ξ‖ = ‖ξ‖} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact hD.induction (P := fun ξ => ‖T ξ‖ = ‖ξ‖)
      (fun v hv => by
        have := hT ⟨v, hv⟩
        simp only at this
        rw [this, hT₀norm]
        rfl) hclosed ξ
  let V : H →ₗᵢ[ℂ] H' := ⟨(T : H →ₗ[ℂ] H'), hTnorm⟩
  have hVx : ∀ i, V (x i) = y i := by
    intro i
    have h1 : Lx (Finsupp.single i 1) = x i := by simp [Lx]
    have h2 : Ly (Finsupp.single i 1) = y i := by simp [Ly]
    have h3 := hT ⟨Lx (Finsupp.single i 1), LinearMap.mem_range_self Lx _⟩
    rw [hT₀, h2] at h3
    simp only [h1] at h3
    exact h3
  have hsurj : Function.Surjective V := by
    have hcl : IsClosed (Set.range V) :=
      V.isometry.isClosedEmbedding.isClosed_range
    have hsub : (Submodule.span ℂ (Set.range y) : Set H') ⊆ Set.range V := by
      have : Submodule.span ℂ (Set.range y) ≤ LinearMap.range V.toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨x i, hVx i⟩
      intro v hv
      obtain ⟨ξ, hξ⟩ := this hv
      exact ⟨ξ, hξ⟩
    have : Set.range V = Set.univ :=
      Set.eq_univ_of_univ_subset (hy.closure_eq ▸ closure_minimal hsub hcl)
    exact Set.range_eq_univ.1 this
  exact ⟨LinearIsometryEquiv.ofSurjective V hsurj, fun i => hVx i⟩
end YangMills.Construction.GramUnitary
