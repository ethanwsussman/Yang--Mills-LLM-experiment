import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.GradientsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.PsiOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheLogOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SplitOfASettingIsRegular
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps RenormalizationStepParameters StepSettings BlockOffsets Interpolation
section Index
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
private theorem sum_freeBondsAt_eq_sum_offsets (hodd : Odd R.params.side) (free : Finset (TorusBond (n * R.params.side)))
    (Y : TorusSite n) {M : Type} [AddCommMonoid M] (g : free → M) :
    ∑ b ∈ freeBondsAt free Y, g b = ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
      (if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ free then g ⟨_, h⟩ else 0) := by
  symm
  set f : (Fin 4 → ℤ) × Fin 4 → M := fun p =>
    if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ free then g ⟨_, h⟩ else 0 with hfdef
  have hf : ∀ p, f p ≠ 0 → nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ free := by
    intro p hne
    by_contra h
    exact hne (dif_neg h)
  refine Finset.sum_bij_ne_zero (f := f) (g := g) (fun p _ hne => ⟨_, hf p hne⟩) ?_ ?_ ?_ ?_
  · intro p hp hne
    simp only [freeBondsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    show parentBlock R.params.side (fineSite R.params.side Y 0 p.1) = Y
    rw [parentBlock_fineSite hodd Y 0 p.1 (Finset.mem_product.mp hp).1]
    have z : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rw [z, add_zero]
  · intro p hp hne p' hp' hne' e
    have e1 := Prod.ext_iff.mp (congrArg Subtype.val e)
    have e2 : fineSite R.params.side Y 0 p.1 = fineSite R.params.side Y 0 p'.1 := e1.1
    have e3 : p.2 = p'.2 := e1.2
    exact Prod.ext (fineSite_injective Y 0 hodd (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp').1 e2) e3
  · intro b hb hgb
    have hblock : parentBlock R.params.side b.1.1 = Y := (Finset.mem_filter.mp hb).2
    obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd Y b.1.1 hblock
    have hnb : nearBond R.params.side Y ((0 : Fin 4 → ℤ), o, b.1.2) = b.1 := Prod.ext e.symm rfl
    have hmem : nearBond R.params.side Y ((0 : Fin 4 → ℤ), o, b.1.2) ∈ free := hnb ▸ b.2
    have hval : f (o, b.1.2) = g b := by
      show (if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), o, b.1.2) ∈ free then g ⟨_, h⟩ else 0) = g b
      rw [dif_pos hmem]
      congr 1
      exact Subtype.ext hnb
    refine ⟨(o, b.1.2), Finset.mem_product.mpr ⟨ho, Finset.mem_univ _⟩, ?_, Subtype.ext hnb⟩
    rw [hval]
    exact hgb
  · intro p _ hne
    exact dif_pos (hf p hne)
private theorem card_offsets (hodd : Odd R.params.side) :
    ((centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) = 4 * (R.params.side : ℝ) ^ 4 := by
  rw [Finset.card_product, card_centredCube hodd]
  simp
  ring
end Index
section Segments
variable {R : StepSetup} {n n' : ℕ} {free : Finset (TorusBond (n * R.params.side))}
  {free' : Finset (TorusBond (n' * R.params.side))}
private theorem update_eq_add_smul_singleBond (ζ : FreeCoords free) (b : free) (X : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    Function.update ζ b (ζ b + τ • X) = ζ + τ • singleBond b (fun _ => X) := by
  classical
  funext b'
  by_cases h : b' = b
  · subst h
    simp [singleBond]
  · simp [singleBond, h]
private theorem singleBond_eq_const (b : free) (η : FreeCoords free) : singleBond b η = singleBond b (fun _ => η b) := by
  classical
  funext b'
  by_cases h : b' = b
  · subst h
    simp [singleBond]
  · simp [singleBond, h]
private theorem singleBond_const_smul (b : free) (c : ℝ) (X : EuclideanSpace ℝ (Fin 3)) :
    singleBond b (fun _ => c • X) = c • singleBond b (fun _ : free => X) := by
  classical
  funext b'
  by_cases h : b' = b
  · subst h
    simp [singleBond]
  · simp [singleBond, h]
private theorem directionalDeriv_eq_fderiv {C : FreeCoords free → ℝ} {U : Set (FreeCoords free)} (hUo : IsOpen U)
    (hC : ContDiffOn ℝ 1 C U) {ζ : FreeCoords free} (hζ : ζ ∈ U) (b : free) (X : EuclideanSpace ℝ (Fin 3)) :
    directionalDeriv C ζ b X = fderiv ℝ C ζ (singleBond b (fun _ => X)) := by
  unfold directionalDeriv
  simp only [update_eq_add_smul_singleBond]
  exact deriv_comp_add_smul_eq_fderiv hUo hC _ hζ
private theorem fderiv_singleBond_eq {C : FreeCoords free → ℝ} {U : Set (FreeCoords free)} (hUo : IsOpen U)
    (hC : ContDiffOn ℝ 1 C U) {ζ η : FreeCoords free} (hζ : ζ ∈ U) (b : free) :
    fderiv ℝ C ζ (singleBond b η) = ‖η b‖ * directionalDeriv C ζ b ((‖η b‖)⁻¹ • η b) := by
  rw [directionalDeriv_eq_fderiv hUo hC hζ]
  by_cases h0 : η b = 0
  · rw [singleBond_eq_const, h0]
    have z : singleBond b (fun _ : free => (0 : EuclideanSpace ℝ (Fin 3))) = 0 := by
      have := singleBond_const_smul (free := free) b 0 (0 : EuclideanSpace ℝ (Fin 3))
      simpa using this
    simp [z]
  · have hn : ‖η b‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    rw [singleBond_eq_const b η]
    have e : η b = ‖η b‖ • ((‖η b‖)⁻¹ • η b) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    conv_lhs => rw [e, singleBond_const_smul, map_smul]
    simp
private theorem norm_inv_norm_smul_self {w : EuclideanSpace ℝ (Fin 3)} (h : w ≠ 0) : ‖(‖w‖)⁻¹ • w‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
private theorem mul_abs_segment_sub_le {C : FreeCoords free → ℝ} {C' : FreeCoords free' → ℝ} {U : Set (FreeCoords free)}
    {U' : Set (FreeCoords free')} (hUo : IsOpen U) (hUo' : IsOpen U') (hC : ContDiffOn ℝ 1 C U)
    (hC' : ContDiffOn ℝ 1 C' U') {η : FreeCoords free} {η' : FreeCoords free'}
    (hs : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U) (hs' : ∀ v ∈ Icc (0 : ℝ) 1, v • η' ∈ U') (b : free) (b' : free')
    (hw : η b = η' b') {e x : ℝ} (hx : 0 < x)
    (he : ∀ v ∈ Icc (0 : ℝ) 1, ∀ X : EuclideanSpace ℝ (Fin 3), ‖X‖ = 1 →
      x * |directionalDeriv C (v • η) b X - directionalDeriv C' (v • η') b' X| ≤ e) :
    x * |(∫ v in (0 : ℝ)..1, fderiv ℝ C (v • η) (singleBond b η)) -
      ∫ v in (0 : ℝ)..1, fderiv ℝ C' (v • η') (singleBond b' η')| ≤ ‖η b‖ * e := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_fderiv_smul_segment hUo hC hs _)
    (intervalIntegrable_fderiv_smul_segment hUo' hC' hs' _)]
  have hb : ∀ v ∈ uIoc (0 : ℝ) 1, ‖fderiv ℝ C (v • η) (singleBond b η) - fderiv ℝ C' (v • η') (singleBond b' η')‖ ≤
      ‖η b‖ * e / x := by
    intro v hv
    rw [uIoc_of_le zero_le_one] at hv
    have hv' : v ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hv
    rw [fderiv_singleBond_eq hUo hC (hs v hv') b, fderiv_singleBond_eq hUo' hC' (hs' v hv') b', ← hw, ← mul_sub,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    by_cases h0 : η b = 0
    · simp [h0]
    · have := he v hv' _ (norm_inv_norm_smul_self h0)
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [le_div_iff₀ hx, mul_comm]
      exact this
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h1
  calc x * _ ≤ x * (‖η b‖ * e / x) := mul_le_mul_of_nonneg_left h1 hx.le
    _ = ‖η b‖ * e := by field_simp
private theorem abs_segment_le {C : FreeCoords free → ℝ} {U : Set (FreeCoords free)} (hUo : IsOpen U)
    (hC : ContDiffOn ℝ 1 C U) {η : FreeCoords free} (hs : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U) (b : free)
    {K : ℝ} (hK : ∀ v ∈ Icc (0 : ℝ) 1, ∀ X : EuclideanSpace ℝ (Fin 3), ‖X‖ = 1 →
      |directionalDeriv C (v • η) b X| ≤ K) :
    |∫ v in (0 : ℝ)..1, fderiv ℝ C (v • η) (singleBond b η)| ≤ ‖η b‖ * K := by
  have hb : ∀ v ∈ uIoc (0 : ℝ) 1, ‖fderiv ℝ C (v • η) (singleBond b η)‖ ≤ ‖η b‖ * K := by
    intro v hv
    rw [uIoc_of_le zero_le_one] at hv
    have hv' : v ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hv
    rw [fderiv_singleBond_eq hUo hC (hs v hv') b, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    by_cases h0 : η b = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hK v hv' _ (norm_inv_norm_smul_self h0)) (norm_nonneg _)
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using h1
end Segments
theorem blockInteractionLocality_of_bounds (hcost : BlockCostsAgree) (hgrad : SettingGradientsClose)
    (hreg : DensitySplitRegular) (hrows : CostHessianFloor)
    (hsize : LogJacobianBound) : blockInteractionLocalityBound := by
  obtain ⟨r₁, p₁, g₁⟩ := hgrad
  obtain ⟨r₂, p₂, g₂⟩ := hreg
  obtain ⟨r₃, p₃, g₃⟩ := hrows
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (p₁ c) (lt_min (p₂ c) (p₃ c)),
    fun T hD hrt => ?_⟩
  have a₁ : T.rt ≤ r₁ T.toChainParameters := hrt.trans (min_le_left _ _)
  have a₂ : T.rt ≤ r₂ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have a₃ : T.rt ≤ r₃ T.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y₁, G⟩ := g₁ T hD a₁
  obtain ⟨y₂, Rg⟩ := g₂ T hD a₂
  obtain ⟨C₃, y₃, hC₃, Hs⟩ := g₃ T hD a₃
  obtain ⟨C₄, y₄, hC₄, Sz⟩ := hsize T hD
  have hlam : 0 < T.lam := hD.chain.2.2.1
  have hσ := hD.σ_pos
  have hρT : 0 < T.ballRadius := by
    unfold ParameterAssignment.ballRadius
    positivity
  have hL0 : (0 : ℝ) < T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.side)
  set K : ℝ := 4 * (T.side : ℝ) ^ 4 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K * T.ballRadius + K * T.ballRadius * C₃ + 2 * C₄ + T.lam / 2 * K * T.ballRadius ^ 2 + 1,
    max (max (max T.floorMin y₁) (max y₂ y₃)) (max y₄ 1), by positivity,
    fun y hy R hR n n' _ _ hn hn' s s' Y Y' m k η η' hs hs' hag hk4 hkm hrk hnear hb hb' => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hy))
  have hy1 : y₁ ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hy))
  have hy2 : y₂ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hy3 : y₃ ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))
  have hy4 : y₄ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy5 : (1 : ℝ) ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hxy := hR.le_coupling
  have hx1 : 1 ≤ R.coupling := hy5.trans hxy
  have hx : 0 < R.coupling := by linarith
  have hfit : R.params.Admissible := hR.params_eq ▸ hD.fits y hy0
  have hodd : Odd R.params.side := hfit.L_odd
  have hLq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hσq : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hρq : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hσq]
  have hreg₁ : s.densitySplit.IsRegular := Rg y ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))) R hR n hn s hs
  have hreg₂ : s'.densitySplit.IsRegular := Rg y ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hy))) R hR n' hn' s' hs'
  obtain ⟨U, hUo, hUb, hC⟩ := hreg₁.cost_smooth
  obtain ⟨U', hUo', hUb', hC'⟩ := hreg₂.cost_smooth
  have hbc : η ∈ closedBallsIn R s.free := hb
  have hbc' : η' ∈ closedBallsIn R s'.free := hb'
  have hseg : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U := fun v hv => hUb _ (smul_mem_closedBallsIn hbc hv)
  have hseg' : ∀ v ∈ Icc (0 : ℝ) 1, v • η' ∈ U' := fun v hv => hUb' _ (smul_mem_closedBallsIn hbc' hv)
  have hscale : ∀ v : ℝ, CoordsAgreeNear s s' Y Y' k (v • η) (v • η') := by
    intro v q hq
    have h1 := hnear q hq
    simp only [ChartSetting.coordsByIndex] at h1 ⊢
    by_cases h : nearBond R.params.side Y q ∈ s.free
    · by_cases h' : nearBond R.params.side Y' q ∈ s'.free
      · rw [dif_pos h, dif_pos h'] at h1 ⊢
        simp only [Pi.smul_apply, h1]
      · rw [dif_pos h, dif_neg h'] at h1 ⊢
        simp only [Pi.smul_apply, h1, smul_zero]
    · by_cases h' : nearBond R.params.side Y' q ∈ s'.free
      · rw [dif_neg h, dif_pos h'] at h1 ⊢
        simp only [Pi.smul_apply, ← h1, smul_zero]
      · rw [dif_neg h, dif_neg h']
  have hcost₁ := hcost T hD y R hy0 hR.params_eq n n' hn hn' s s' Y Y' m k η η' hs hs' hag hk4 hkm hnear hb hb'
  have h00 : CoordsAgreeNear s s' Y Y' k 0 0 := by
    have := hscale 0
    simpa using this
  have hz : s.InBalls 0 := by
    have h1 : (0 : ℝ) • η ∈ closedBallsIn R s.free := smul_mem_closedBallsIn hbc (by simp)
    rw [zero_smul] at h1
    exact h1
  have hz' : s'.InBalls 0 := by
    have h1 : (0 : ℝ) • η' ∈ closedBallsIn R s'.free := smul_mem_closedBallsIn hbc' (by simp)
    rw [zero_smul] at h1
    exact h1
  have hcost₀ := hcost T hD y R hy0 hR.params_eq n n' hn hn' s s' Y Y' m k 0 0 hs hs' hag hk4 hkm h00 hz hz'
  have hpsi : s.blockInteraction Y η = R.coupling * ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η -
      s.logJacobianAt Y η + s.logJacobianAt Y 0 :=
    interaction_eq hreg₁ hbc Y
  have hpsi' : s'.blockInteraction Y' η' = R.coupling * ∑ b ∈ freeBondsAt s'.free Y', s'.densitySplit.segmentIntegral b η' -
      s'.logJacobianAt Y' η' + s'.logJacobianAt Y' 0 := interaction_eq hreg₂ hbc' Y'
  have hq : s.blockGaussian T.lam Y η = R.coupling * T.lam / 2 * ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 := rfl
  have hq' : s'.blockGaussian T.lam Y' η' = R.coupling * T.lam / 2 * ∑ b ∈ freeBondsAt s'.free Y', ‖η' b‖ ^ 2 := rfl
  have hnorm : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => by
    have := hb b
    rwa [coordNorm_eq_norm, hρq] at this
  classical
  constructor
  · rw [hpsi, hpsi', hq, hq', sum_freeBondsAt_eq_sum_offsets hodd s.free Y, sum_freeBondsAt_eq_sum_offsets hodd s'.free Y',
      sum_freeBondsAt_eq_sum_offsets hodd s.free Y, sum_freeBondsAt_eq_sum_offsets hodd s'.free Y', hcost₁.2.1, hcost₀.2.1]
    have hterm : ∀ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
        R.coupling * |(if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free then
            s.densitySplit.segmentIntegral ⟨_, h⟩ η else 0) -
          (if h : nearBond R.params.side Y' ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s'.free then
            s'.densitySplit.segmentIntegral ⟨_, h⟩ η' else 0)| ≤ T.ballRadius * Real.exp (-(4 * T.rt * k)) ∧
        (if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free then ‖η ⟨_, h⟩‖ ^ 2 else 0) =
          (if h : nearBond R.params.side Y' ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s'.free then ‖η' ⟨_, h⟩‖ ^ 2 else 0) := by
      intro p hp
      have hnq : IsNearIndex R.params.side (k / 2) ((0 : Fin 4 → ℤ), p.1, p.2) :=
        ⟨fun i => by simp only [Pi.zero_apply, abs_zero]; exact Int.natCast_nonneg _, (Finset.mem_product.mp hp).1⟩
      have hnk : IsNearIndex R.params.side k ((0 : Fin 4 → ℤ), p.1, p.2) :=
        ⟨fun i => by simp only [Pi.zero_apply, abs_zero]; exact Int.natCast_nonneg _, (Finset.mem_product.mp hp).1⟩
      have hnm : IsNearIndex R.params.side m ((0 : Fin 4 → ℤ), p.1, p.2) :=
        ⟨fun i => by simp only [Pi.zero_apply, abs_zero]; exact Int.natCast_nonneg _, (Finset.mem_product.mp hp).1⟩
      by_cases h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free
      · have h' := (hag.free_iff _ hnm).mp h
        rw [dif_pos h, dif_pos h', dif_pos h, dif_pos h']
        have hw : η ⟨_, h⟩ = η' ⟨_, h'⟩ := by
          have h1 := hnear _ hnk
          simp only [ChartSetting.coordsByIndex] at h1
          rwa [dif_pos h, dif_pos h'] at h1
        refine ⟨?_, by rw [hw]⟩
        have hcl := mul_abs_segment_sub_le (C := s.densitySplit.totalCost) (C' := s'.densitySplit.totalCost) hUo hUo' hC hC' hseg hseg'
          ⟨_, h⟩ ⟨_, h'⟩ hw hx (e := Real.exp (-(4 * T.rt * k))) (fun v hv X hX => ?_)
        · refine hcl.trans ?_
          exact mul_le_mul_of_nonneg_right (hnorm _) (Real.exp_pos _).le
        · exact (G y hy1 R hR n n' hn hn' s s' Y Y' m k (v • η) (v • η')
            hs hs' hag hkm hrk (hscale v) (smul_mem_closedBallsIn hbc hv) (smul_mem_closedBallsIn hbc' hv) _ h h' X hnq hX).1
      · have h' : nearBond R.params.side Y' ((0 : Fin 4 → ℤ), p.1, p.2) ∉ s'.free :=
          fun hh => h ((hag.free_iff _ hnm).mpr hh)
        rw [dif_neg h, dif_neg h', dif_neg h, dif_neg h']
        simp
        exact mul_nonneg hρT.le (Real.exp_pos _).le
    have hB : ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
        (if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free then ‖η ⟨_, h⟩‖ ^ 2 else 0) =
        ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
        (if h : nearBond R.params.side Y' ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s'.free then ‖η' ⟨_, h⟩‖ ^ 2 else 0) :=
      Finset.sum_congr rfl fun p hp => (hterm p hp).2
    rw [hB]
    set A := ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
      (if h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free then
        s.densitySplit.segmentIntegral ⟨_, h⟩ η else 0) with hA
    set A' := ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
      (if h : nearBond R.params.side Y' ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s'.free then
        s'.densitySplit.segmentIntegral ⟨_, h⟩ η' else 0) with hA'
    have hdiff : |R.coupling * A - R.coupling * A'| ≤ K * T.ballRadius * Real.exp (-(4 * T.rt * k)) := by
      rw [← mul_sub, hA, hA', ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hx]
      calc R.coupling * |∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), _|
          ≤ R.coupling * ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), |_| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hx.le
        _ = ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), R.coupling * |_| := Finset.mul_sum _ _ _
        _ ≤ ∑ _p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
              T.ballRadius * Real.exp (-(4 * T.rt * k)) :=
            Finset.sum_le_sum fun p hp => (hterm p hp).1
        _ = K * T.ballRadius * Real.exp (-(4 * T.rt * k)) := by
            rw [Finset.sum_const, nsmul_eq_mul, card_offsets hodd, hLq, hK]
            ring
    have hexp := Real.exp_pos (-(4 * T.rt * (k : ℝ)))
    have hKρ : K * T.ballRadius ≤
        K * T.ballRadius + K * T.ballRadius * C₃ + 2 * C₄ + T.lam / 2 * K * T.ballRadius ^ 2 + 1 := by
      have : 0 ≤ K * T.ballRadius * C₃ := by positivity
      have h2 : 0 ≤ T.lam / 2 * K * T.ballRadius ^ 2 := by positivity
      linarith
    have e : ∀ c d g : ℝ, (R.coupling * A - c + d - g) - (R.coupling * A' - c + d - g) =
        R.coupling * A - R.coupling * A' := by
      intro c d g
      ring
    rw [e]
    exact hdiff.trans (mul_le_mul_of_nonneg_right hKρ hexp.le)
  · have hrow := Hs y hy3 R hR n hn s hs
    have hj₁ := Sz y R hR.params_eq hR.anchorRadius_eq (hy4.trans hxy) n s Y η hb
    have hj₀ := Sz y R hR.params_eq hR.anchorRadius_eq (hy4.trans hxy) n s Y 0 hz
    have hlog : Real.log R.coupling ≤ R.coupling := Real.log_le_self hx.le
    have hj₁' : |s.logJacobianAt Y η| ≤ C₄ * R.coupling := hj₁.trans (mul_le_mul_of_nonneg_left hlog hC₄.le)
    have hj₀' : |s.logJacobianAt Y 0| ≤ C₄ * R.coupling := hj₀.trans (mul_le_mul_of_nonneg_left hlog hC₄.le)
    have hseg₁ : ∀ b : s.free, |s.densitySplit.segmentIntegral b η| ≤ T.ballRadius * C₃ := by
      intro b
      have h1 := abs_segment_le (C := s.densitySplit.totalCost) hUo hC hseg b (K := C₃) fun v hv X hX =>
        hrow.firstDeriv_le (v • η) (smul_mem_closedBallsIn hbc hv) b X hX
      exact h1.trans (mul_le_mul_of_nonneg_right (hnorm b) hC₃.le)
    have hS : |∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η| ≤ K * (T.ballRadius * C₃) := by
      rw [sum_freeBondsAt_eq_sum_offsets hodd s.free Y]
      calc |∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), _|
          ≤ ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), |_| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), T.ballRadius * C₃ := by
            refine Finset.sum_le_sum fun p _ => ?_
            by_cases h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free
            · rw [dif_pos h]
              exact hseg₁ _
            · rw [dif_neg h, abs_zero]
              positivity
        _ = K * (T.ballRadius * C₃) := by
            rw [Finset.sum_const, nsmul_eq_mul, card_offsets hodd, hLq, hK]
    have hQ₀ : 0 ≤ ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hQ₁ : ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 ≤ K * T.ballRadius ^ 2 := by
      rw [sum_freeBondsAt_eq_sum_offsets hodd s.free Y]
      calc ∑ p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), _
          ≤ ∑ _p ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)), T.ballRadius ^ 2 := by
            refine Finset.sum_le_sum fun p _ => ?_
            by_cases h : nearBond R.params.side Y ((0 : Fin 4 → ℤ), p.1, p.2) ∈ s.free
            · rw [dif_pos h]
              exact pow_le_pow_left₀ (norm_nonneg _) (hnorm _) 2
            · rw [dif_neg h]
              positivity
        _ = K * T.ballRadius ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, card_offsets hodd, hLq, hK]
    rw [hpsi, hq]
    set S := ∑ b ∈ freeBondsAt s.free Y, s.densitySplit.segmentIntegral b η with hSdef
    set Q := ∑ b ∈ freeBondsAt s.free Y, ‖η b‖ ^ 2 with hQdef
    have hsx : |R.coupling * S| ≤ R.coupling * (K * (T.ballRadius * C₃)) := by
      rw [abs_mul, abs_of_pos hx]
      exact mul_le_mul_of_nonneg_left hS hx.le
    have hqx : |R.coupling * T.lam / 2 * Q| ≤ R.coupling * (T.lam / 2 * K * T.ballRadius ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      have : R.coupling * T.lam / 2 * Q = R.coupling * (T.lam / 2 * Q) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ hx.le
      have h2 : T.lam / 2 * Q ≤ T.lam / 2 * (K * T.ballRadius ^ 2) := mul_le_mul_of_nonneg_left hQ₁ (by positivity)
      linarith
    have hCx : R.coupling * (K * (T.ballRadius * C₃)) + C₄ * R.coupling + C₄ * R.coupling +
          R.coupling * (T.lam / 2 * K * T.ballRadius ^ 2) ≤
        (K * T.ballRadius + K * T.ballRadius * C₃ + 2 * C₄ + T.lam / 2 * K * T.ballRadius ^ 2 + 1) * R.coupling := by
      have hpos : 0 ≤ (K * T.ballRadius + 1) * R.coupling := by positivity
      have e : (K * T.ballRadius + K * T.ballRadius * C₃ + 2 * C₄ + T.lam / 2 * K * T.ballRadius ^ 2 + 1) * R.coupling =
          R.coupling * (K * (T.ballRadius * C₃)) + C₄ * R.coupling + C₄ * R.coupling +
            R.coupling * (T.lam / 2 * K * T.ballRadius ^ 2) + (K * T.ballRadius + 1) * R.coupling := by
        ring
      linarith
    rw [abs_le] at hsx hqx hj₁' hj₀' ⊢
    constructor <;> linarith [hsx.1, hsx.2, hqx.1, hqx.2, hj₁'.1, hj₁'.2, hj₀'.1, hj₀'.2]
end YangMills.Construction.ClusterExpansionOfAStep
end
