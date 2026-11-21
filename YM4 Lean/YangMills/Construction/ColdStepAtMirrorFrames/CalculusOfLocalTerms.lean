import YangMills.Construction.ClusterExpansionOfAStep.PartsOfTheCostAlongMoves
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfACutMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.SizesUnderAGoodExponent
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus
variable {ι κ P : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype P] {ρ : ℝ}
theorem openPolyball_eq_ball (hρ : 0 < ρ) : openPolyball ι ρ = Metric.ball (0 : BondField ι) ρ := by
  ext η
  simp only [openPolyball, Set.mem_ofPred_eq, mem_ball_zero_iff]
  exact (pi_norm_lt_iff hρ).symm
theorem isOpen_openPolyball (hρ : 0 < ρ) : IsOpen (openPolyball ι ρ) := by
  rw [openPolyball_eq_ball hρ]
  exact Metric.isOpen_ball
theorem convex_openPolyball (hρ : 0 < ρ) : Convex ℝ (openPolyball ι ρ) := by
  rw [openPolyball_eq_ball hρ]
  exact convex_ball _ _
theorem zero_mem_openPolyball (hρ : 0 < ρ) : (0 : BondField ι) ∈ openPolyball ι ρ := fun b => by simpa using hρ
theorem abs_fderiv_bondVariation_le (f : BondField ι → ℝ) (b : ι) (η : BondField ι) (v : BondVector) :
    |fderiv ℝ f η (bondVariation b v)| ≤ bondGradNorm f b η * ‖v‖ := by
  unfold bondGradNorm
  have := ((fderiv ℝ f η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm v
  simpa [bondVariation] using this
theorem bondGradNorm_le_of_forall {f : BondField ι → ℝ} {b : ι} {η : BondField ι} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, |fderiv ℝ f η (bondVariation b v)| ≤ C * ‖v‖) : bondGradNorm f b η ≤ C := by
  unfold bondGradNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  simpa [bondVariation] using h v
theorem bondGradNorm_nonneg (f : BondField ι → ℝ) (b : ι) (η : BondField ι) :
    0 ≤ bondGradNorm f b η := norm_nonneg _
theorem clm_apply_eq_sum_bondVariation (L : BondField ι →L[ℝ] ℝ) (u : BondField ι) :
    L u = ∑ b, L (bondVariation b (u b)) := by apply _root_.YangMills.Construction.CostDerivatives.linear_eq_sum_single <;> assumption
theorem abs_sub_le_sum_bondGradNorm (hρ : 0 < ρ) {G : BondField ι → ℝ} (hG : ContDiffOn ℝ 1 G (openPolyball ι ρ))
    {η ζ : BondField ι} (hη : η ∈ openPolyball ι ρ) (hζ : ζ ∈ openPolyball ι ρ) (C : ι → ℝ)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b, bondGradNorm G b (ζ + s • (η - ζ)) ≤ C b) :
    |G η - G ζ| ≤ ∑ b, C b * ‖η b - ζ b‖ := by
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ζ + s • (η - ζ) ∈ openPolyball ι ρ := by
    intro s hs
    have := (convex_openPolyball (ι := ι) hρ).add_smul_sub_mem hζ hη hs
    exact this
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => G (ζ + s • (η - ζ)))
      (fderiv ℝ G (ζ + s • (η - ζ)) (η - ζ)) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have h1 : HasFDerivAt G (fderiv ℝ G (ζ + s • (η - ζ))) (ζ + s • (η - ζ)) :=
      ((hG.contDiffAt ((isOpen_openPolyball hρ).mem_nhds (hseg s hs))).differentiableAt
        (by norm_num)).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => ζ + s • (η - ζ)) (η - ζ) s := by
      have := ((hasDerivAt_id s).smul_const (η - ζ)).const_add ζ
      simpa using this
    exact (h1.comp_hasDerivAt s h2).hasDerivWithinAt
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (C := ∑ b, C b * ‖η b - ζ b‖) hder
    (fun s hs => by
      rw [Real.norm_eq_abs, clm_apply_eq_sum_bondVariation]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (abs_fderiv_bondVariation_le G b _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hC s hs b) (norm_nonneg _))
    (convex_Icc 0 1) (by simp) (by simp)
  simpa using key
def restrictToBondsCLM (Λ : Finset ι) : BondField ι →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => if b ∈ Λ then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b else 0
theorem restrictToBondsCLM_apply (Λ : Finset ι) (η : BondField ι) : restrictToBondsCLM Λ η = restrictToBonds Λ η := by
  funext b
  by_cases h : b ∈ Λ <;> simp [restrictToBondsCLM, restrictToBonds, h]
def pushforwardFieldCLM (j : κ → ι) : BondField κ →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => ∑ k, if j k = b then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => BondVector) k else 0
theorem pushforwardFieldCLM_apply (j : κ → ι) (ξ : BondField κ) : pushforwardFieldCLM j ξ = pushforwardField j ξ := by
  funext b
  simp only [pushforwardFieldCLM, pushforwardField, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : j k = b <;> simp [h]
theorem pushforwardField_apply_image (j : κ → ι) (hj : Function.Injective j) (ξ : BondField κ) (k : κ) :
    pushforwardField j ξ (j k) = ξ k := by
  unfold pushforwardField
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hne
    have h1 : j k' ≠ j k := fun h => hne (hj h)
    simp [h1]
  · simp
theorem pushforwardField_apply_of_not_mem_range (j : κ → ι) (ξ : BondField κ) (b : ι) (h : ∀ k, j k ≠ b) :
    pushforwardField j ξ b = 0 := by
  unfold pushforwardField
  simp [h]
theorem pushforwardField_bondVariation (j : κ → ι) (hj : Function.Injective j) (k : κ) (v : BondVector) :
    pushforwardField j (bondVariation k v) = bondVariation (j k) v := by
  funext b
  by_cases h : ∃ k', j k' = b
  · obtain ⟨k', rfl⟩ := h
    rw [pushforwardField_apply_image j hj]
    by_cases e : k' = k
    · subst e
      simp [bondVariation]
    · have : j k' ≠ j k := fun h => e (hj h)
      simp [bondVariation, e, this]
  · push Not at h
    rw [pushforwardField_apply_of_not_mem_range j _ b h]
    have : b ≠ j k := fun e => h k e.symm
    simp [bondVariation, this]
theorem pushforwardField_mem_openPolyball (hρ : 0 < ρ) (j : κ → ι) (hj : Function.Injective j) {ξ : BondField κ}
    (h : ξ ∈ openPolyball κ ρ) : pushforwardField j ξ ∈ openPolyball ι ρ := by
  intro b
  by_cases hb : ∃ k, j k = b
  · obtain ⟨k, rfl⟩ := hb
    rw [pushforwardField_apply_image j hj]
    exact h k
  · push Not at hb
    rw [pushforwardField_apply_of_not_mem_range j _ b hb]
    simpa using hρ
theorem restrictToBonds_mem_openPolyball (hρ : 0 < ρ) (Λ : Finset ι) {η : BondField ι} (h : η ∈ openPolyball ι ρ) :
    restrictToBonds Λ η ∈ openPolyball ι ρ := by
  intro b
  by_cases hb : b ∈ Λ
  · simpa [restrictToBonds, hb] using h b
  · simpa [restrictToBonds, hb] using hρ
theorem restrictToBonds_bondVariation_of_mem (Λ : Finset ι) {b : ι} (hb : b ∈ Λ) (v : BondVector) :
    restrictToBonds Λ (bondVariation b v) = bondVariation b v := by
  funext c
  by_cases h : c ∈ Λ
  · simp [restrictToBonds, h]
  · have : c ≠ b := fun e => h (e ▸ hb)
    simp [restrictToBonds, h, bondVariation, this]
theorem restrictToBonds_bondVariation_of_not_mem (Λ : Finset ι) {b : ι} (hb : b ∉ Λ) (v : BondVector) :
    restrictToBonds Λ (bondVariation b v) = 0 := by
  funext c
  by_cases h : c ∈ Λ
  · have : c ≠ b := fun e => hb (e ▸ h)
    simp [restrictToBonds, h, bondVariation, this]
  · simp [restrictToBonds, h]
theorem fderiv_comp_clm_apply (hρ : 0 < ρ) {θ : BondField ι → ℝ} (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (L : BondField κ →L[ℝ] BondField ι) {ξ : BondField κ} (h : L ξ ∈ openPolyball ι ρ)
    (u : BondField κ) : fderiv ℝ (fun ζ => θ (L ζ)) ξ u = fderiv ℝ θ (L ξ) (L u) := by
  have h1 : HasFDerivAt θ (fderiv ℝ θ (L ξ)) (L ξ) :=
    ((hθ.contDiffAt ((isOpen_openPolyball hρ).mem_nhds h)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 := h1.comp ξ L.hasFDerivAt
  have e : (fun ζ => θ (L ζ)) = θ ∘ L := rfl
  rw [e, h2.fderiv]
  rfl
theorem bondGradNorm_comp_clm_le (hρ : 0 < ρ) {θ : BondField ι → ℝ} (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (L : BondField κ →L[ℝ] BondField ι) {ξ : BondField κ} (h : L ξ ∈ openPolyball ι ρ)
    {k : κ} {b : ι} (hL : ∀ v, L (bondVariation k v) = bondVariation b v) :
    bondGradNorm (fun ζ => θ (L ζ)) k ξ ≤ bondGradNorm θ b (L ξ) := by
  apply bondGradNorm_le_of_forall (bondGradNorm_nonneg _ _ _)
  intro v
  rw [fderiv_comp_clm_apply hρ hθ L h, hL]
  exact abs_fderiv_bondVariation_le θ b _ v
theorem bondGradNorm_comp_clm_eq_zero (hρ : 0 < ρ) {θ : BondField ι → ℝ} (hθ : ContDiffOn ℝ 1 θ (openPolyball ι ρ))
    (L : BondField κ →L[ℝ] BondField ι) {ξ : BondField κ} (h : L ξ ∈ openPolyball ι ρ)
    {k : κ} (hL : ∀ v, L (bondVariation k v) = 0) : bondGradNorm (fun ζ => θ (L ζ)) k ξ = 0 := by
  apply le_antisymm _ (bondGradNorm_nonneg _ _ _)
  apply bondGradNorm_le_of_forall le_rfl
  intro v
  rw [fderiv_comp_clm_apply hρ hθ L h, hL]
  simp
theorem bondGradNorm_linear_combination_le (hρ : 0 < ρ) {f g : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ))
    (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ)) (a c : ℝ) {η : BondField ι} (hη : η ∈ openPolyball ι ρ) (b : ι) :
    bondGradNorm (fun ζ => a * f ζ + c * g ζ) b η ≤ |a| * bondGradNorm f b η + |c| * bondGradNorm g b η := by
  have h1 : HasFDerivAt f (fderiv ℝ f η) η :=
    ((hf.contDiffAt ((isOpen_openPolyball hρ).mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 : HasFDerivAt g (fderiv ℝ g η) η :=
    ((hg.contDiffAt ((isOpen_openPolyball hρ).mem_nhds hη)).differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun ζ => a * f ζ + c * g ζ) (a • fderiv ℝ f η + c • fderiv ℝ g η) η :=
    (h1.const_mul a).add (h2.const_mul c)
  apply bondGradNorm_le_of_forall (by have := bondGradNorm_nonneg f b η; have := bondGradNorm_nonneg g b η; positivity)
  intro v
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, add_mul, mul_assoc, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left (abs_fderiv_bondVariation_le f b η v) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (abs_fderiv_bondVariation_le g b η v) (abs_nonneg _))
section NearSquare
variable {r : ℝ} {pos : ι → P} {D : P → P → ℝ}
theorem weightedSqNormNear_nonneg (z : P) (η : BondField ι) : 0 ≤ weightedSqNormNear r pos D z η :=
  Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)
theorem isBoundedContinuousOn_weightedSqNormNear (hρ : 0 < ρ) (z : P) :
    IsBoundedContinuousOn ι ρ (weightedSqNormNear r pos D z) := by
  unfold weightedSqNormNear
  exact IsBoundedContinuousOn.sum _ _ fun b _ =>
    (IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)
theorem weightedSqNormNear_mono (z : P) {η ζ : BondField ι} (h : ∀ b, ‖η b‖ ≤ ‖ζ b‖) :
    weightedSqNormNear r pos D z η ≤ weightedSqNormNear r pos D z ζ := by
  refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact pow_le_pow_left₀ (norm_nonneg _) (h b) 2
end NearSquare
section Expectations
variable {m r S : ℝ} {p : ℝ → ℝ} {pos : ι → P} {D : P → P → ℝ} {Ψ : BondField ι → ℝ}
theorem abs_ballExpectation_le (F : IsPositiveUnitalForm ρ p Ψ) {f g : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f)
    (hg : IsBoundedContinuousOn ι ρ g) (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤ g η) :
    |ballExpectation (cutoffFactor ρ p) Ψ f| ≤ ballExpectation (cutoffFactor ρ p) Ψ g := by
  have hu := F.mono f g hf hg fun η hη => (le_abs_self _).trans (h η hη)
  have hl := F.mono (fun η => (-1) * g η) f (by simpa using hg.neg) hf
    (fun η hη => by linarith [neg_abs_le (f η), h η hη])
  rw [F.map_smul] at hl
  exact _root_.abs_le.mpr ⟨by linarith, hu⟩
theorem ballL2Norm_le_of_expectation_sq_le (h : BondField ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hm : ballExpectation (cutoffFactor ρ p) Ψ (fun η => h η ^ 2) ≤ C ^ 2) :
    ballL2Norm (cutoffFactor ρ p) Ψ h ≤ C := by
  unfold ballL2Norm
  rw [show C = Real.sqrt (C ^ 2) from (Real.sqrt_sq hC).symm]
  exact Real.sqrt_le_sqrt hm
theorem ballL2Norm_le_of_near_majorant (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p Ψ)
    (Sz : AdmissibleMomentBounds ρ m r S p pos D Ψ) {h : BondField ι → ℝ} (hn : IsBoundedContinuousOn ι ρ h)
    {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (z : P)
    (hh : ∀ η ∈ openPolyball ι ρ, |h η| ≤ a * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1)) :
    ballL2Norm (cutoffFactor ρ p) Ψ h ≤ a * Real.sqrt (2 * x ^ 2 * (8 * S ^ 2 / m) + 2) := by
  have hq := isBoundedContinuousOn_weightedSqNormNear (r := r) (pos := pos) (D := D) (ι := ι) hρ z
  have hnear := Sz.near_moment_le z
  have hqm : 0 ≤ ballExpectation (cutoffFactor ρ p) Ψ (weightedSqNormNear r pos D z) := by
    have h0 := F.mono (fun _ => 0) _ (IsBoundedContinuousOn.const 0) hq (fun η _ => weightedSqNormNear_nonneg z η)
    rwa [F.map_zero] at h0
  have hGn : 0 ≤ 2 * x ^ 2 * (8 * S ^ 2 / m) + 2 := by
    have : 0 ≤ 8 * S ^ 2 / m := hqm.trans hnear
    positivity
  apply ballL2Norm_le_of_expectation_sq_le h (by positivity)
  have hsq : IsBoundedContinuousOn ι ρ (fun η => h η ^ 2) := by
    have := hn.mul hn
    simpa [pow_two] using this
  have hmaj : IsBoundedContinuousOn ι ρ (fun η => a ^ 2 * (2 * x ^ 2) * weightedSqNormNear r pos D z η + a ^ 2 * 2) :=
    ((IsBoundedContinuousOn.const _).mul hq).add (IsBoundedContinuousOn.const _)
  have hle := F.mono _ _ hsq hmaj (fun η hη => by
    have h1 := hh η hη
    have hs := weightedSqNormNear_nonneg (r := r) (pos := pos) (D := D) z η
    set u := Real.sqrt (weightedSqNormNear r pos D z η) with hu
    have hu2 : u ^ 2 = weightedSqNormNear r pos D z η := Real.sq_sqrt hs
    have h2 : h η ^ 2 ≤ (a * (x * u + 1)) ^ 2 := by
      rw [← sq_abs (h η)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (a * (x * u + 1)) ^ 2 ≤ a ^ 2 * (2 * x ^ 2) * u ^ 2 + a ^ 2 * 2 := by
      have : (x * u + 1) ^ 2 ≤ 2 * x ^ 2 * u ^ 2 + 2 := by nlinarith [sq_nonneg (x * u - 1)]
      calc (a * (x * u + 1)) ^ 2 = a ^ 2 * (x * u + 1) ^ 2 := by ring
        _ ≤ a ^ 2 * (2 * x ^ 2 * u ^ 2 + 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    rw [← hu2]
    exact h2.trans h3)
  refine hle.trans ?_
  rw [F.map_add _ _ ((IsBoundedContinuousOn.const _).mul hq) (IsBoundedContinuousOn.const _), F.map_smul]
  have e1 : ballExpectation (cutoffFactor ρ p) Ψ (fun _ => a ^ 2 * 2) = a ^ 2 * 2 := by
    have := F.map_smul (a ^ 2 * 2) (fun _ => 1)
    rw [F.map_one] at this
    simpa using this
  rw [e1, mul_pow, Real.sq_sqrt hGn]
  have : a ^ 2 * (2 * x ^ 2) * ballExpectation (cutoffFactor ρ p) Ψ (weightedSqNormNear r pos D z) ≤
      a ^ 2 * (2 * x ^ 2) * (8 * S ^ 2 / m) := mul_le_mul_of_nonneg_left hnear (by positivity)
  nlinarith
theorem ballL2Norm_le_of_linear_majorant (hρ : 0 < ρ) (F : IsPositiveUnitalForm ρ p Ψ)
    (Sz : AdmissibleMomentBounds ρ m r S p pos D Ψ) (hS : 0 ≤ S) (hm : 0 < m) {h : BondField ι → ℝ}
    (hn : IsBoundedContinuousOn ι ρ h) (a : ι → ℝ) (ha : ∀ b, 0 ≤ a b)
    (hh : ∀ η ∈ openPolyball ι ρ, |h η| ≤ ∑ b, a b * ‖η b‖) :
    ballL2Norm (cutoffFactor ρ p) Ψ h ≤ (∑ b, a b) * Real.sqrt (8 * S / m) := by
  have hA : 0 ≤ ∑ b, a b := Finset.sum_nonneg fun b _ => ha b
  have hq : 0 ≤ 8 * S / m := by positivity
  apply ballL2Norm_le_of_expectation_sq_le h (by positivity)
  have hsq : IsBoundedContinuousOn ι ρ (fun η => h η ^ 2) := by
    have := hn.mul hn
    simpa [pow_two] using this
  have hlin : IsBoundedContinuousOn ι ρ (fun η => (∑ b, a b * ‖η b‖) ^ 2) := by
    refine ⟨?_, (∑ b, a b * ρ) ^ 2, fun η hη => ?_⟩
    · apply Continuous.continuousOn
      exact (continuous_finsetSum _ fun b _ =>
        continuous_const.mul (continuous_apply b).norm).pow 2
    · rw [abs_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => mul_nonneg (ha b) (norm_nonneg _))
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hη b).le (ha b)
  have hle := F.mono _ _ hsq hlin (fun η hη => by
    rw [← sq_abs (h η)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hh η hη) 2)
  refine hle.trans ((Sz.linear_moment_le a ha).trans ?_)
  rw [mul_pow, Real.sq_sqrt hq]
theorem ballCovariance_congr (F : IsPositiveUnitalForm ρ p Ψ) {f f' g g' : BondField ι → ℝ}
    (hf : ∀ η ∈ openPolyball ι ρ, f η = f' η) (hg : ∀ η ∈ openPolyball ι ρ, g η = g' η) :
    ballCovariance (cutoffFactor ρ p) Ψ f g = ballCovariance (cutoffFactor ρ p) Ψ f' g' := by
  unfold ballCovariance
  rw [F.congr_on f f' hf, F.congr_on g g' hg,
    F.congr_on (fun η => f η * g η) (fun η => f' η * g' η) (fun η hη => by rw [hf η hη, hg η hη])]
theorem ballCovariance_sum_right {α : Type} (F : IsPositiveUnitalForm ρ p Ψ) {f : BondField ι → ℝ}
    (hf : IsBoundedContinuousOn ι ρ f)
    (s : Finset α) (g : α → BondField ι → ℝ) (hg : ∀ a ∈ s, IsBoundedContinuousOn ι ρ (g a)) :
    ballCovariance (cutoffFactor ρ p) Ψ f (fun η => ∑ a ∈ s, g a η) =
      ∑ a ∈ s, ballCovariance (cutoffFactor ρ p) Ψ f (g a) := by
  unfold ballCovariance
  simp only [Finset.mul_sum]
  rw [F.map_sum s (fun a η => f η * g a η) (fun a ha => hf.mul (hg a ha)), F.map_sum s g hg, Finset.mul_sum,
    Finset.sum_sub_distrib]
theorem ballCovariance_sub_right (F : IsPositiveUnitalForm ρ p Ψ) {f g h : BondField ι → ℝ}
    (hf : IsBoundedContinuousOn ι ρ f) (hg : IsBoundedContinuousOn ι ρ g) (hh : IsBoundedContinuousOn ι ρ h) :
    ballCovariance (cutoffFactor ρ p) Ψ f (fun η => g η - h η) =
      ballCovariance (cutoffFactor ρ p) Ψ f g - ballCovariance (cutoffFactor ρ p) Ψ f h := by
  unfold ballCovariance
  have e : (fun η => f η * (g η - h η)) = fun η => f η * g η - f η * h η := by
    funext η
    ring
  rw [e, F.map_sub (hf.mul hg) (hf.mul hh), F.map_sub hg hh]
  ring
theorem abs_ballCovariance_le_of_decay (hρ : 0 < ρ) (hr : 0 < r) (hD : IsPseudoMetricOnBonds D)
    (Sz : AdmissibleMomentBounds ρ m r S p pos D Ψ) (hm : 0 < m)
    (hS : ∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S)
    {f g : BondField ι → ℝ} {M A B : ℝ} {z z' : P}
    (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ))
    (hb : ∀ η ∈ openPolyball ι ρ, |f η| ≤ M ∧ |g η| ≤ M ∧
      ∀ b, bondGradNorm f b η ≤ M ∧ bondGradNorm g b η ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfn : ∀ b, ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) ≤ A * Real.exp (-(2 * r * D (pos b) z)))
    (hgn : ∀ b, ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b) ≤ B * Real.exp (-(2 * r * D (pos b) z'))) :
    |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤ m⁻¹ * A * S * (B * S * Real.exp (-(r / 2 * D z' z))) := by
  have h := Sz.covariance_le f g M A z (fun b => B * Real.exp (-(2 * r * D (pos b) z'))) hf hg hb hA
    (fun b => by positivity) hfn hgn
  refine h.trans ?_
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le).trans (hS z)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hnn : ∀ y w, 0 ≤ D y w := fun y w => by
    have h1 := hD.triangle y w y
    rw [hD.self, hD.symm w y] at h1
    linarith
  calc ∑ b, B * Real.exp (-(2 * r * D (pos b) z')) * Real.exp (-(r / 2 * D (pos b) z))
      ≤ ∑ b, B * (Real.exp (-(r / 4 * D (pos b) z')) * Real.exp (-(r / 2 * D z' z))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hB
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have t1 := hD.triangle z' (pos b) z
        rw [hD.symm z' (pos b)] at t1
        have t2 := hnn (pos b) z'
        nlinarith
    _ = B * (∑ b, Real.exp (-(r / 4 * D (pos b) z'))) * Real.exp (-(r / 2 * D z' z)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ B * S * Real.exp (-(r / 2 * D z' z)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hS z') hB
end Expectations
section LocalTermBounds
variable {r c x : ℝ} {pos : ι → P} {D : P → P → ℝ} {z : P} {θ : BondField ι → ℝ}
theorem pseudoMetric_nonneg (hD : IsPseudoMetricOnBonds D) (y w : P) : 0 ≤ D y w := by
  have h1 := hD.triangle y w y
  rw [hD.self, hD.symm w y] at h1
  linarith
theorem exists_bondGradNorm_bound_of_localTerm (hρ : 0 < ρ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hD : IsPseudoMetricOnBonds D) (hθ : IsLocalTermAt ρ r c x pos D z θ) :
    ∃ M, 0 ≤ M ∧ ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm θ b η ≤ M := by
  obtain ⟨hcn, Q, hQ⟩ := isBoundedContinuousOn_weightedSqNormNear (r := r) (pos := pos) (D := D) (ι := ι) hρ z
  refine ⟨c * (x * Real.sqrt Q + 1), by positivity, fun η hη b => ?_⟩
  refine (hθ.slope η hη b).trans ?_
  have h1 : Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := pseudoMetric_nonneg hD (pos b) z
    have : 0 ≤ 2 ^ 5 * r * D (pos b) z := by positivity
    linarith
  have h2 : Real.sqrt (weightedSqNormNear r pos D z η) ≤ Real.sqrt Q :=
    Real.sqrt_le_sqrt ((le_abs_self _).trans (hQ η hη))
  calc c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z))
      ≤ c * (x * Real.sqrt Q + 1) * 1 := by
        apply mul_le_mul _ h1 (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hc
        have := mul_le_mul_of_nonneg_left h2 hx
        linarith
    _ = _ := mul_one _
theorem contDiffOn_one_of_two (hθ : ContDiffOn ℝ 2 θ (openPolyball ι ρ)) : ContDiffOn ℝ 1 θ (openPolyball ι ρ) :=
  hθ.of_le (by norm_num)
theorem isBoundedContinuousOn_of_bondGradNorm_le (hρ : 0 < ρ) {G : BondField ι → ℝ}
    (hG : ContDiffOn ℝ 1 G (openPolyball ι ρ)) {M : ℝ}
    (hMn : 0 ≤ M) (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm G b η ≤ M) : IsBoundedContinuousOn ι ρ G := by
  refine ⟨hG.continuousOn, |G 0| + ∑ _b : ι, M * ρ, fun η hη => ?_⟩
  have h0 := zero_mem_openPolyball (ι := ι) hρ
  have h1 := abs_sub_le_sum_bondGradNorm hρ hG hη h0 (fun _ => M) (fun s hs b => by
    apply hM
    have := (convex_openPolyball (ι := ι) hρ).add_smul_sub_mem h0 hη hs
    exact this)
  have h2 : ∑ b, M * ‖η b - (0 : BondField ι) b‖ ≤ ∑ _b : ι, M * ρ :=
    Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (by simpa using (hη b).le) hMn
  have h3 := abs_sub_abs_le_abs_sub (G η) (G 0)
  linarith
theorem continuousOn_bondGradNorm (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ))
    (b : ι) : ContinuousOn (bondGradNorm f b) (openPolyball ι ρ) := by
  unfold bondGradNorm
  have := hf.continuousOn_fderiv_of_isOpen (isOpen_openPolyball hρ) (by norm_num)
  exact (this.clm_comp continuousOn_const).norm
theorem isBoundedContinuousOn_bondGradNorm (hρ : 0 < ρ) {f : BondField ι → ℝ}
    (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ)) {M : ℝ}
    (hM : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm f b η ≤ M) (b : ι) : IsBoundedContinuousOn ι ρ (bondGradNorm f b) :=
  ⟨continuousOn_bondGradNorm hρ hf b, M, fun η hη => by
    rw [abs_of_nonneg (bondGradNorm_nonneg f b η)]
    exact hM η hη b⟩
theorem exists_common_bound (hρ : 0 < ρ) {f g : BondField ι → ℝ} (hf : ContDiffOn ℝ 1 f (openPolyball ι ρ))
    (hg : ContDiffOn ℝ 1 g (openPolyball ι ρ)) {Mf Mg : ℝ} (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hf' : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm f b η ≤ Mf)
    (hg' : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm g b η ≤ Mg) :
    ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M ∧ |g η| ≤ M ∧
      ∀ b, bondGradNorm f b η ≤ M ∧ bondGradNorm g b η ≤ M := by
  obtain ⟨_, A, hA⟩ := isBoundedContinuousOn_of_bondGradNorm_le hρ hf hMf hf'
  obtain ⟨_, B, hB⟩ := isBoundedContinuousOn_of_bondGradNorm_le hρ hg hMg hg'
  refine ⟨|A| + |B| + Mf + Mg, fun η hη => ⟨?_, ?_, fun b => ⟨?_, ?_⟩⟩⟩
  · have := hA η hη
    have := le_abs_self A
    have := abs_nonneg B
    linarith
  · have := hB η hη
    have := le_abs_self B
    have := abs_nonneg A
    linarith
  · have := hf' η hη b
    have := abs_nonneg A
    have := abs_nonneg B
    linarith
  · have := hg' η hη b
    have := abs_nonneg A
    have := abs_nonneg B
    linarith
end LocalTermBounds
theorem contDiff_norm_sq_apply (b : ι) : ContDiff ℝ 3 (fun η : BondField ι => ‖η b‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b)
theorem contDiff_halfSqNormOn (μ : ℝ) (Λ : Finset ι) : ContDiff ℝ 3 (halfSqNormOn (ι := ι) μ Λ) := by
  unfold halfSqNormOn
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul (contDiff_norm_sq_apply b)
theorem fderiv_halfSqNormOn_apply (μ : ℝ) (Λ : Finset ι) (ζ u : BondField ι) :
    fderiv ℝ (halfSqNormOn μ Λ) ζ u = ∑ b ∈ Λ, μ * inner ℝ (ζ b) (u b) := by
  have hb : ∀ b ∈ Λ, HasFDerivAt (fun η : BondField ι => μ / 2 * ‖η b‖ ^ 2)
      ((μ / 2) • (2 • (innerSL ℝ (ζ b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b))) ζ := by
    intro b _
    have h1 : HasFDerivAt (fun η : BondField ι => η b)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b) ζ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
    exact (h1.norm_sq).const_mul (μ / 2)
  have h := HasFDerivAt.fun_sum hb
  have e : HasFDerivAt (halfSqNormOn μ Λ) _ ζ := h
  rw [e.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro b _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring
theorem bondGradNorm_halfSqNormOn_le {μ : ℝ} (hμ : 0 ≤ μ) (Λ : Finset ι) (η : BondField ι) (b : ι) :
    bondGradNorm (halfSqNormOn μ Λ) b η ≤ if b ∈ Λ then μ * ‖η b‖ else 0 := by
  apply bondGradNorm_le_of_forall (by split_ifs <;> positivity)
  intro v
  rw [fderiv_halfSqNormOn_apply]
  by_cases hb : b ∈ Λ
  · rw [Finset.sum_eq_single b]
    · simp only [bondVariation, Pi.single_eq_same, hb, if_true]
      rw [abs_mul, abs_of_nonneg hμ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hμ
    · intro c _ hc
      simp [bondVariation, hc]
    · exact fun h => absurd hb h
  · rw [Finset.sum_eq_zero]
    · simp [hb]
    · intro c hc
      have : c ≠ b := fun h => hb (h ▸ hc)
      simp [bondVariation, this]
end YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus
end
