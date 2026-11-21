import YangMills.Construction.ClusterExpansionOfAStep.ConvexAtRateOnFewerBonds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RestrictedPotentials
open ColdStepAtMirrorFrames
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
def extendByZeroLinear (e : ι' → ι) (he : Function.Injective e) : BondField ι' →ₗ[ℝ] BondField ι where
  toFun ξ := Function.extend e ξ 0
  map_add' ξ ζ := by
    funext b
    by_cases h : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := h
      simp [he.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_smul' t ξ := by
    funext b
    by_cases h : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := h
      simp [he.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
def extendByZeroCLM (e : ι' → ι) (he : Function.Injective e) : BondField ι' →L[ℝ] BondField ι :=
  LinearMap.toContinuousLinearMap (extendByZeroLinear e he)
theorem extendByZeroCLM_apply (e : ι' → ι) (he : Function.Injective e) (ξ : BondField ι') :
    extendByZeroCLM e he ξ = Function.extend e ξ 0 := rfl
theorem extendByZeroCLM_bondVariation (e : ι' → ι) (he : Function.Injective e) (b : ι') (X : BondVector) :
    extendByZeroCLM e he (bondVariation b X) = bondVariation (e b) X := by
  rw [extendByZeroCLM_apply]
  funext x
  by_cases h : ∃ b', e b' = x
  · obtain ⟨b', rfl⟩ := h
    rw [he.extend_apply]
    by_cases hb : b' = b
    · subst hb
      simp [bondVariation]
    · have : e b' ≠ e b := fun h => hb (he h)
      simp [bondVariation, Pi.single_eq_of_ne hb, Pi.single_eq_of_ne this]
  · rw [Function.extend_apply' _ _ _ h]
    have : x ≠ e b := fun hx => h ⟨b, hx.symm⟩
    simp [bondVariation, Pi.single_eq_of_ne this]
theorem hasFDerivAt_extendByHeld (e : ι' → ι) (he : Function.Injective e) (c : BondField ι) (ξ : BondField ι') :
    HasFDerivAt (extendByHeld e c) (extendByZeroCLM e he) ξ := by
  have h1 : (extendByHeld e c) = fun ξ => c + extendByZeroCLM e he ξ := rfl
  rw [h1]
  exact (extendByZeroCLM e he).hasFDerivAt.const_add c
theorem fderiv_comp_extendByHeld {g : BondField ι → ℝ} (hg : Differentiable ℝ g) (e : ι' → ι)
    (he : Function.Injective e) (c : BondField ι) (ξ : BondField ι') :
    fderiv ℝ (fun ξ => g (extendByHeld e c ξ)) ξ = (fderiv ℝ g (extendByHeld e c ξ)).comp (extendByZeroCLM e he) :=
  ((hg _).hasFDerivAt.comp ξ (hasFDerivAt_extendByHeld e he c ξ)).fderiv
theorem secondDerivAlong_comp_extendByHeld {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (e : ι' → ι)
    (he : Function.Injective e) (c : BondField ι) (ξ u v : BondField ι') :
    secondDerivAlong (fun ξ => Ψ (extendByHeld e c ξ)) ξ u v =
      secondDerivAlong Ψ (extendByHeld e c ξ) (extendByZeroCLM e he u) (extendByZeroCLM e he v) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fun ζ => fderiv ℝ Ψ ζ (extendByZeroCLM e he u)) :=
    ((hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  unfold secondDerivAlong
  have h0 : (fun ζ => fderiv ℝ (fun ξ => Ψ (extendByHeld e c ξ)) ζ u) =
      fun ζ => fderiv ℝ Ψ (extendByHeld e c ζ) (extendByZeroCLM e he u) := by
    funext ζ
    rw [fderiv_comp_extendByHeld hd e he c ζ]
    rfl
  rw [h0, fderiv_comp_extendByHeld hdf e he c ξ]
  rfl
theorem uniformlyConvexOnSubfamily_holds : UniformlyConvexOnSubfamily := by
  intro ι ι' _ _ _ _ e ρ m κ d Ψ K c he hρ hκ hd hconv hc hc0
  have hΨd : Differentiable ℝ Ψ := hconv.smooth.differentiable (by norm_num)
  have hheld : ∀ (ξ : BondField ι'), (∀ b, ‖ξ b‖ < ρ) → ∀ b, ‖extendByHeld e c ξ b‖ < ρ := by
    intro ξ hξ b
    by_cases h : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := h
      simp only [extendByHeld, Pi.add_apply, hc0, zero_add, he.extend_apply]
      exact hξ b'
    · simp only [extendByHeld, Pi.add_apply, Function.extend_apply' _ _ _ h, Pi.zero_apply, add_zero]
      exact hc b
  have hdn : ∀ b b', 0 ≤ d b b' := by
    intro b b'
    have h1 := hd.triangle b b' b
    rw [hd.self b, hd.symm b' b] at h1
    linarith
  have hK0 : ∀ b b', 0 ≤ K b b' := by
    intro b b'
    have hx : ∃ X : BondVector, ‖X‖ = 1 := by
      refine ⟨EuclideanSpace.single 0 1, ?_⟩
      simp
    obtain ⟨X, hX⟩ := hx
    have h1 := hconv.kernel 0 (fun b => by simpa using hρ) b b' X X
    rw [hX, mul_one, mul_one] at h1
    exact (abs_nonneg _).trans h1
  refine ⟨⟨?_, fun ξ hξ u => ?_, fun ξ hξ b b' x x' => ?_, fun b b' => hconv.symm _ _, fun b => ?_⟩, ?_⟩
  · have : (fun ξ => Ψ (extendByHeld e c ξ)) = fun ξ => Ψ (c + extendByZeroCLM e he ξ) := rfl
    rw [this]
    exact hconv.smooth.comp (contDiff_const.add (extendByZeroCLM e he).contDiff)
  · rw [secondDerivAlong_comp_extendByHeld hconv.smooth e he]
    refine le_trans ?_ (hconv.floor _ (hheld ξ hξ) (extendByZeroCLM e he u))
    have hs : ∑ b, ‖u b‖ ^ 2 = ∑ b, ‖extendByZeroCLM e he u b‖ ^ 2 := by
      refine Fintype.sum_of_injective e he _ _ (fun x hx => ?_) (fun b => ?_)
      · rw [extendByZeroCLM_apply, Function.extend_apply' _ _ _ (by simpa using hx)]
        simp
      · rw [extendByZeroCLM_apply, he.extend_apply]
    rw [hs]
  · rw [secondDerivAlong_comp_extendByHeld hconv.smooth e he, extendByZeroCLM_bondVariation,
      extendByZeroCLM_bondVariation]
    exact hconv.kernel _ (hheld ξ hξ) _ _ _ _
  · have h1 := hconv.standingConstraints (e b)
    refine le_trans ?_ h1
    have hinj : Set.InjOn e (Finset.univ : Finset ι') := he.injOn
    have h2 : ∑ b', K (e b) (e b') * (Real.exp (2 * κ * d (e b) (e b')) - 1) =
        ∑ x ∈ Finset.univ.image e, K (e b) x * (Real.exp (2 * κ * d (e b) x) - 1) := by
      rw [Finset.sum_image hinj]
    rw [h2]
    refine Finset.sum_le_univ_sum_of_nonneg fun x => mul_nonneg (hK0 _ _) ?_
    have : 0 ≤ 2 * κ * d (e b) x := mul_nonneg (by linarith) (hdn _ _)
    have := Real.add_one_le_exp (2 * κ * d (e b) x)
    linarith
  · intro ξ b X
    rw [fderiv_comp_extendByHeld hΨd e he c ξ]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [extendByZeroCLM_bondVariation]
end YangMills.Construction.RestrictedPotentials
end
