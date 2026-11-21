import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Towers.PropertiesOfTheSymbolOfOneStepProof
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreePropertiesProof
import YangMills.Construction.TwoPoints.TranslationModulusOfAFunction
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace TranslationModulusLemmas
theorem euclidNorm_nonneg_of_point (x : AmbientSpace) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem sup_norm_le_euclidNorm (x : AmbientSpace) : ‖x‖ ≤ euclidNorm x := by apply _root_.YangMills.Construction.TwoPoints.AdmissibleFormConsequences.norm_le_euclidNorm <;> assumption
theorem euclidNorm_neg_eq (x : AmbientSpace) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]
theorem hermitianNorm_le_two_mul_sup (z : Fin 4 → ℂ) : hermitianNorm z ≤ 2 * ‖z‖ := by apply _root_.YangMills.Construction.Tower.StepEntryBounds.euclidNorm_le_two_mul_norm <;> assumption
theorem partialDerivR4_eq_fderiv {F : AmbientSpace → ℂ} (hF : Differentiable ℝ F) (i : Fin 4)
    (x : AmbientSpace) :
    TestFunctions.partialDerivR4 i F x = fderiv ℝ F x (Pi.single i (1 : ℝ)) := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.partialDerivR4_eq_fderiv <;> assumption
theorem fderiv_apply_eq_sum_grad {F : AmbientSpace → ℂ} (hF : Differentiable ℝ F)
    (x h : AmbientSpace) :
    fderiv ℝ F x h = ∑ i, (h i : ℂ) * grad F x i := by
  have hh : h = ∑ i, h i • (Pi.single i (1 : ℝ) : AmbientSpace) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hh]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  simp only [grad, partialDerivR4_eq_fderiv hF]
theorem norm_sum_ofReal_mul_le (h : AmbientSpace) (z : Fin 4 → ℂ) :
    ‖∑ i, (h i : ℂ) * z i‖ ≤ euclidNorm h * hermitianNorm z := by
  calc ‖∑ i, (h i : ℂ) * z i‖ ≤ ∑ i, |h i| * ‖z i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        simp
    _ ≤ Real.sqrt (∑ i, |h i| ^ 2) * Real.sqrt (∑ i, ‖z i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = euclidNorm h * hermitianNorm z := by
        simp [euclidNorm, hermitianNorm, sq_abs]
theorem norm_sub_le_of_grad_bound {F : AmbientSpace → ℂ} (hF : Differentiable ℝ F) {C : ℝ}
    (hC : ∀ x, hermitianNorm (grad F x) ≤ C) (x y : AmbientSpace) :
    ‖F x - F y‖ ≤ C * euclidNorm (x - y) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => F (y + u • (x - y)))
      (fderiv ℝ F (y + t • (x - y)) (x - y)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => y + u • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact ((hF _).hasFDerivAt.comp_hasDerivAt t h1)
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ F (y + t • (x - y)) (x - y)‖ ≤
      C * euclidNorm (x - y) := by
    intro t _
    rw [fderiv_apply_eq_sum_grad hF]
    refine (norm_sum_ofReal_mul_le _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (euclidNorm_nonneg_of_point _)
  have := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa using this
theorem grad_translateFun (v : AmbientSpace) (F : AmbientSpace → ℂ) (x : AmbientSpace) :
    grad (translateFun v F) x = grad F (x - v) := by
  funext i
  simp only [grad, TestFunctions.partialDerivR4, translateFun]
  congr 1
  funext t
  congr 1
  abel
theorem differentiable_translateFun {F : AmbientSpace → ℂ} (hF : Differentiable ℝ F)
    (v : AmbientSpace) : Differentiable ℝ (translateFun v F) :=
  hF.comp (differentiable_id.sub_const v)
theorem grad_sub_of_differentiable {F G : AmbientSpace → ℂ} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (x : AmbientSpace) : grad (F - G) x = grad F x - grad G x := by
  funext i
  have h : fderiv ℝ (F - G) x = fderiv ℝ F x - fderiv ℝ G x :=
    ((hF x).hasFDerivAt.sub (hG x).hasFDerivAt).fderiv
  simp only [grad, Pi.sub_apply, partialDerivR4_eq_fderiv (hF.sub hG),
    partialDerivR4_eq_fderiv hF, partialDerivR4_eq_fderiv hG, h]
  rfl
theorem continuous_grad {f : AmbientSpace → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (grad f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  refine continuous_pi fun i => ?_
  have h : (fun x => grad f x i) = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
    funext x
    exact partialDerivR4_eq_fderiv hd i x
  rw [h]
  exact hc.clm_apply continuous_const
theorem hasCompactSupport_grad {f : AmbientSpace → ℂ} (hf : ContDiff ℝ 1 f)
    (hk : HasCompactSupport f) : HasCompactSupport (grad f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h : grad f =
      (fun L : AmbientSpace →L[ℝ] ℂ => fun i : Fin 4 => L (Pi.single i (1 : ℝ))) ∘ fderiv ℝ f := by
    funext x i
    exact partialDerivR4_eq_fderiv hd i x
  rw [h]
  exact (hk.fderiv (𝕜 := ℝ)).comp_left rfl
theorem exists_grad_bound {f : AmbientSpace → ℂ} (hf : ContDiff ℝ 1 f) (hk : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖grad f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_grad hf).bounded_above_of_compact_support
    (hasCompactSupport_grad hf hk)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
theorem gradSupENN_lt_top {f : AmbientSpace → ℂ} (hf : ContDiff ℝ 1 f) (hk : HasCompactSupport f) :
    gradSupENN f < ∞ := by
  obtain ⟨C, -, hC⟩ := exists_grad_bound hf hk
  refine lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := 2 * C))
  refine ENNReal.ofReal_le_ofReal ((hermitianNorm_le_two_mul_sup _).trans ?_)
  linarith [hC x]
theorem gradOscENNReal_lt_top {f : AmbientSpace → ℂ} (hf : ContDiff ℝ 1 f)
    (hk : HasCompactSupport f) (δ : ℝ) : gradOscENNReal f δ < ∞ := by
  obtain ⟨C, -, hC⟩ := exists_grad_bound hf hk
  refine lt_of_le_of_lt (iSup_le fun x => iSup_le fun x' => iSup_le fun _ => ?_)
    (ENNReal.ofReal_lt_top (r := 4 * C))
  refine ENNReal.ofReal_le_ofReal ((hermitianNorm_le_two_mul_sup _).trans ?_)
  have := norm_sub_le (grad f x) (grad f x')
  linarith [hC x, hC x']
theorem hermitianNorm_grad_le_gradSup {f : AmbientSpace → ℂ} (h : gradSupENN f < ∞)
    (x : AmbientSpace) : hermitianNorm (grad f x) ≤ gradSup f :=
  (ENNReal.ofReal_le_iff_le_toReal h.ne).1
    (le_iSup (fun x => ENNReal.ofReal (gradNorm f x)) x)
theorem hermitianNorm_grad_sub_le_gradOsc {f : AmbientSpace → ℂ} {δ : ℝ}
    (h : gradOscENNReal f δ < ∞) {x x' : AmbientSpace} (hx : euclidNorm (x - x') ≤ δ) :
    hermitianNorm (grad f x - grad f x') ≤ gradOsc f δ := by
  refine (ENNReal.ofReal_le_iff_le_toReal h.ne).1 ?_
  exact le_iSup_of_le x (le_iSup_of_le x' (le_iSup_of_le hx le_rfl))
theorem gradOscENNReal_mono (f : AmbientSpace → ℂ) {a b : ℝ} (hab : a ≤ b) :
    gradOscENNReal f a ≤ gradOscENNReal f b :=
  iSup_le fun x => iSup_le fun x' => iSup_le fun h =>
    le_iSup_of_le x (le_iSup_of_le x' (le_iSup_of_le (h.trans hab) le_rfl))
theorem tendsto_gradOsc_zero {f : AmbientSpace → ℂ} (hu : UniformContinuous (grad f)) :
    Tendsto (gradOsc f) (𝓝[>] 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨d, hd, hud⟩ := Metric.uniformContinuous_iff.1 hu (ε / 4) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ
  have hle : gradOsc f δ ≤ ε / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine iSup_le fun x => iSup_le fun x' => iSup_le fun h => ?_
    refine ENNReal.ofReal_le_ofReal ((hermitianNorm_le_two_mul_sup _).trans ?_)
    have h1 : dist x x' < d := by
      rw [dist_eq_norm]
      exact ((sup_norm_le_euclidNorm _).trans h).trans_lt hδ.2
    have h2 := hud h1
    rw [dist_eq_norm] at h2
    linarith
  have hn : 0 ≤ gradOsc f δ := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith
theorem euclidNorm_sub_sub_eq (x v v' : AmbientSpace) :
    euclidNorm ((x - v) - (x - v')) = euclidNorm (v - v') := by
  rw [← euclidNorm_neg_eq (v - v')]
  congr 1
  abel
theorem sharpNorm_translateFun_sub_le (S : FixedScale) {f : AmbientSpace → ℂ}
    (hd : Differentiable ℝ f) (hs : gradSupENN f < ∞) (ho : ∀ δ, gradOscENNReal f δ < ∞)
    (v v' : AmbientSpace) :
    S.sharpNorm (translateFun v f - translateFun v' f) ≤
      S.translationModulus f (euclidNorm (v - v')) := by
  have hM : 0 ≤ 40 * S.scale := by linarith [S.scale_pos]
  have hv := differentiable_translateFun hd v
  have hv' := differentiable_translateFun hd v'
  refine max_le_max ?_ (mul_le_mul_of_nonneg_left ?_ hM)
  · refine ciSup_le fun x => ?_
    have h := norm_sub_le_of_grad_bound hd (hermitianNorm_grad_le_gradSup hs) (x - v) (x - v')
    rw [euclidNorm_sub_sub_eq] at h
    exact h
  · refine csInf_le ⟨0, fun C hC => hC.1⟩ ⟨ENNReal.toReal_nonneg, fun x y => ?_⟩
    refine norm_sub_le_of_grad_bound (hv.sub hv') (fun z => ?_) x y
    rw [grad_sub_of_differentiable hv hv', grad_translateFun, grad_translateFun]
    exact hermitianNorm_grad_sub_le_gradOsc (ho _) (euclidNorm_sub_sub_eq z v v').le
end TranslationModulusLemmas
open TranslationModulusLemmas in
theorem TranslationModulusProperties.holds : TranslationModulusProperties.Statement := by
  intro S f hf
  have hf' : ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ univ := hf
  obtain ⟨hc, hk, -⟩ := hf'
  have hk' : HasCompactSupport f := hk
  have hd : Differentiable ℝ f := hc.differentiable (by norm_num)
  have hs := gradSupENN_lt_top hc hk'
  have ho := gradOscENNReal_lt_top hc hk'
  have hM : 0 ≤ 40 * S.scale := by linarith [S.scale_pos]
  have hu : UniformContinuous (grad f) :=
    (hasCompactSupport_grad hc hk').uniformContinuous_of_continuous (continuous_grad hc)
  refine ⟨⟨?_, ?_, hs, fun δ _ => ho δ, sharpNorm_translateFun_sub_le S hd hs ho, ?_⟩, ?_⟩
  · exact ⟨gradSup f, ENNReal.toReal_nonneg,
      norm_sub_le_of_grad_bound hd (hermitianNorm_grad_le_gradSup hs)⟩
  · exact csInf_le ⟨0, fun C hC => hC.1⟩
      ⟨ENNReal.toReal_nonneg, norm_sub_le_of_grad_bound hd (hermitianNorm_grad_le_gradSup hs)⟩
  · have h1 : Tendsto (fun δ : ℝ => gradSup f * δ) (𝓝[>] 0) (𝓝 (gradSup f * 0)) :=
      (tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds
    have h2 := (tendsto_gradOsc_zero hu).const_mul (40 * S.scale)
    have h3 := h1.max h2
    exact show Tendsto (fun δ : ℝ => max (gradSup f * δ) (40 * S.scale * gradOsc f δ))
        (𝓝[>] 0) (𝓝 0) from by simpa using h3
  · intro a ha b hb hab
    refine max_le_max (mul_le_mul_of_nonneg_left hab ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_left ?_ hM)
    exact ENNReal.toReal_mono (ho b).ne (gradOscENNReal_mono f hab)
end YangMills.Construction.TwoPoints
end
