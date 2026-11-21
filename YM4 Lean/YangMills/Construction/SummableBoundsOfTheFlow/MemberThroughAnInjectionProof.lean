import YangMills.Construction.SummableBoundsOfTheFlow.MemberThroughAnInjection
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ConvexRestriction
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
private def extendByZeroCLM (j : ι → ι') : BondField ι →L[ℝ] BondField ι' :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι' => BondVector) (j i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) i)
private theorem extendByZeroCLM_apply (j : ι → ι') (ζ : BondField ι) :
    extendByZeroCLM j ζ = extendByZero j ζ := by
  funext b
  simp only [extendByZeroCLM, extendByZero, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : j i = b
  · subst h; simp
  · have : b ≠ j i := fun e => h e.symm
    simp [h, this]
private theorem extendByZero_apply_image {j : ι → ι'} (hj : Function.Injective j) (ζ : BondField ι) (i : ι) :
    extendByZero j ζ (j i) = ζ i := by
  unfold extendByZero
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi
    rw [if_neg (fun e => hi (hj e))]
  · simp
private theorem extendByZero_apply_of_not_mem_range {j : ι → ι'} (ζ : BondField ι) {b : ι'}
    (hb : ∀ i, j i ≠ b) : extendByZero j ζ b = 0 := by
  unfold extendByZero
  exact Finset.sum_eq_zero fun i _ => if_neg (hb i)
private theorem extendByZero_bondVariation {j : ι → ι'} (hj : Function.Injective j) (i : ι) (e : BondVector) :
    extendByZero j (bondVariation i e) = bondVariation (j i) e := by
  funext b
  by_cases hb : ∃ i', j i' = b
  · obtain ⟨i', rfl⟩ := hb
    rw [extendByZero_apply_image hj]
    by_cases h : i' = i
    · subst h; simp [bondVariation]
    · have : j i' ≠ j i := fun e => h (hj e)
      simp [bondVariation, h, this]
  · push Not at hb
    rw [extendByZero_apply_of_not_mem_range _ hb]
    have : b ≠ j i := fun e => hb i e.symm
    simp [bondVariation, this]
private theorem sum_norm_sq_extendByZero {j : ι → ι'} (hj : Function.Injective j) (u : BondField ι) :
    ∑ b, ‖extendByZero j u b‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  have h1 : ∑ b, ‖extendByZero j u b‖ ^ 2 = ∑ b ∈ Finset.univ.image j, ‖extendByZero j u b‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
    have : ∀ i, j i ≠ b := fun i e => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ i, e⟩)
    rw [extendByZero_apply_of_not_mem_range _ this]
    simp
  rw [h1, Finset.sum_image (fun a _ b _ e => hj e)]
  exact Finset.sum_congr rfl fun i _ => by rw [extendByZero_apply_image hj]
theorem isConvexClassMemberCompInjective : IsConvexClassMemberCompInjective := by
  intro ι ι' _ _ _ _ ρ m κ d d' j P hρ hκ hj hd hd0 hP
  obtain ⟨Ψ, K, hag, hcv, hs⟩ := hP
  set E := extendByZeroCLM j with hE
  have hEa : ∀ ζ, E ζ = extendByZero j ζ := extendByZeroCLM_apply j
  have hΨd : Differentiable ℝ Ψ := hcv.smooth.differentiable (by norm_num)
  have hballs : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < ρ) → ∀ b, ‖extendByZero j ζ b‖ < ρ := by
    intro ζ hζ b
    by_cases hb : ∃ i, j i = b
    · obtain ⟨i, rfl⟩ := hb
      rw [extendByZero_apply_image hj]
      exact hζ i
    · push Not at hb
      rw [extendByZero_apply_of_not_mem_range _ hb]
      simpa using hρ
  have hD : ∀ ζ v, fderiv ℝ (fun ζ => Ψ (E ζ)) ζ v = fderiv ℝ Ψ (E ζ) (E v) := by
    intro ζ v
    have h1 := ((hΨd (E ζ)).hasFDerivAt.comp ζ E.hasFDerivAt).fderiv
    have h2 : (fun ζ => Ψ (E ζ)) = Ψ ∘ E := rfl
    rw [h2, h1]
    rfl
  have h2 : ∀ w : BondField ι', Differentiable ℝ fun y => fderiv ℝ Ψ y w := fun w =>
    ((hcv.smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).clm_apply
      (differentiable_const w)
  have hS : ∀ η u v, secondDerivAlong (fun ζ => Ψ (E ζ)) η u v = secondDerivAlong Ψ (E η) (E u) (E v) := by
    intro η u v
    unfold secondDerivAlong
    have e1 : (fun ζ => fderiv ℝ (fun ζ => Ψ (E ζ)) ζ u) = (fun y => fderiv ℝ Ψ y (E u)) ∘ E := by
      funext ζ
      exact hD ζ u
    rw [e1, ((h2 (E u) (E η)).hasFDerivAt.comp η E.hasFDerivAt).fderiv]
    rfl
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    have h0 : ∀ c, ‖(0 : BondField ι') c‖ < ρ := fun c => by simpa using hρ
    have := hcv.kernel 0 h0 b b' (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    simp only [EuclideanSpace.norm_single, norm_one, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨fun ζ => Ψ (E ζ), fun i i' => K (j i) (j i'), fun ζ hζ => ?_, ⟨hcv.smooth.comp E.contDiff,
    fun η hη u => ?_, fun η hη i i' e e' => ?_, fun i i' => hcv.symm _ _, fun i => ?_⟩, fun i e => ?_⟩
  · simp only [hEa]
    exact hag _ (hballs ζ hζ)
  · rw [hS, hEa η, hEa u]
    have := hcv.floor _ (hballs η hη) (extendByZero j u)
    rwa [sum_norm_sq_extendByZero hj] at this
  · rw [hS, hEa η, hEa, hEa, extendByZero_bondVariation hj, extendByZero_bondVariation hj]
    exact hcv.kernel _ (hballs η hη) _ _ e e'
  · have h1 : ∑ i', K (j i) (j i') * (Real.exp (2 * κ * d i i') - 1) =
        ∑ b' ∈ Finset.univ.image j, K (j i) b' * (Real.exp (2 * κ * d' (j i) b') - 1) := by
      rw [Finset.sum_image (fun a _ b _ e => hj e)]
      exact Finset.sum_congr rfl fun i' _ => by rw [hd]
    rw [h1]
    refine le_trans ?_ (hcv.standingConstraints (j i))
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b' _ _ => ?_
    refine mul_nonneg (hK0 _ _) ?_
    have : 0 ≤ 2 * κ * d' (j i) b' := by have := hd0 (j i) b'; positivity
    have := Real.add_one_le_exp (2 * κ * d' (j i) b')
    linarith
  · unfold bondPartialDeriv
    rw [hD, map_zero, hEa, extendByZero_bondVariation hj]
    exact hs (j i) e
end YangMills.Construction.ConvexRestriction
end
