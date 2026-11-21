import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasure
import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValue
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ValueFreezing
section Cutoff
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ}
theorem polyball_eq_ball (hρ : 0 < ρ) : openPolyball ι ρ = Metric.ball (0 : BondField ι) ρ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.openPolyball_eq_ball <;> assumption
theorem zero_mem_polyball (hρ : 0 < ρ) : (0 : BondField ι) ∈ openPolyball ι ρ := fun b => by simpa using hρ
theorem weightProd_continuous (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    Continuous (radialWeightProd (ι := ι) r) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SegmentMean.continuous_radialWeightProd <;> assumption
theorem weightProd_eq_zero (hr : IsRadialCutoff ρ r) (η : BondField ι) (h : η ∉ openPolyball ι ρ) :
    radialWeightProd r η = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SegmentMean.radialWeightProd_eq_zero <;> assumption
theorem weightProd_pos (hr : IsRadialCutoff ρ r) (η : BondField ι) (h : η ∈ openPolyball ι ρ) :
    0 < radialWeightProd r η :=
  Finset.prod_pos fun b _ => hr.pos _ (norm_nonneg _) (h b)
theorem weightProd_nonneg (hr : IsRadialCutoff ρ r) (η : BondField ι) : 0 ≤ radialWeightProd r η := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.radialWeightProd_nonneg <;> assumption
theorem continuous_density (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) {Ψ : BondField ι → ℝ}
    (hΨ : Continuous Ψ) : Continuous (ballDensity r Ψ) := by
  unfold ballDensity
  exact (weightProd_continuous hρ hr).mul (hΨ.neg.rexp)
theorem compactSupport_density (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) {Ψ : BondField ι → ℝ} :
    HasCompactSupport (ballDensity r Ψ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField ι) ρ) fun η hη => ?_
  have : η ∉ openPolyball ι ρ := fun h => hη (by
    rw [polyball_eq_ball hρ] at h
    exact Metric.ball_subset_closedBall h)
  simp [ballDensity, weightProd_eq_zero hr η this]
theorem nonneg_density (hr : IsRadialCutoff ρ r) {Ψ : BondField ι → ℝ}
    (η : BondField ι) : 0 ≤ ballDensity r Ψ η :=
  mul_nonneg (weightProd_nonneg hr η) (Real.exp_pos _).le
theorem integrable_mul_density (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) {Ψ g : BondField ι → ℝ}
    (hΨ : Continuous Ψ) (hg : Continuous g) : Integrable (fun η => g η * ballDensity r Ψ η) := by
  apply Continuous.integrable_of_hasCompactSupport (hg.mul (continuous_density hρ hr hΨ))
  exact (compactSupport_density hρ hr).mul_left
theorem density_integral_pos (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) {Ψ : BondField ι → ℝ}
    (hΨ : Continuous Ψ) : 0 < ∫ η, ballDensity r Ψ η := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (continuous_density hρ hr hΨ) (compactSupport_density hρ hr) (fun η => nonneg_density hr η)
    (x := 0)
  exact (mul_pos (weightProd_pos hr 0 (zero_mem_polyball hρ)) (Real.exp_pos _)).ne'
theorem expectation_congr (hr : IsRadialCutoff ρ r) {Ψ₁ Ψ₂ f g : BondField ι → ℝ}
    (hΨ : ∀ η ∈ openPolyball ι ρ, Ψ₁ η = Ψ₂ η) (hf : ∀ η ∈ openPolyball ι ρ, f η = g η) :
    ballExpectation r Ψ₁ f = ballExpectation r Ψ₂ g := by
  unfold ballExpectation
  have h1 : ∀ η, f η * ballDensity r Ψ₁ η = g η * ballDensity r Ψ₂ η := fun η => by
    by_cases h : η ∈ openPolyball ι ρ
    · simp [ballDensity, hΨ η h, hf η h]
    · simp [ballDensity, weightProd_eq_zero hr η h]
  have h2 : ∀ η, ballDensity r Ψ₁ η = ballDensity r Ψ₂ η := fun η => by
    by_cases h : η ∈ openPolyball ι ρ
    · simp [ballDensity, hΨ η h]
    · simp [ballDensity, weightProd_eq_zero hr η h]
  simp_rw [h1, h2]
theorem covariance_congr (hr : IsRadialCutoff ρ r) {Ψ₁ Ψ₂ f f' g g' : BondField ι → ℝ}
    (hΨ : ∀ η ∈ openPolyball ι ρ, Ψ₁ η = Ψ₂ η) (hf : ∀ η ∈ openPolyball ι ρ, f η = f' η)
    (hg : ∀ η ∈ openPolyball ι ρ, g η = g' η) : ballCovariance r Ψ₁ f g = ballCovariance r Ψ₂ f' g' := by
  unfold ballCovariance
  rw [expectation_congr hr hΨ (f := fun η => f η * g η) (g := fun η => f' η * g' η)
    (fun η h => by rw [hf η h, hg η h]), expectation_congr hr hΨ hf, expectation_congr hr hΨ hg]
section Linear
variable {Ψ : BondField ι → ℝ} {f g : BondField ι → ℝ}
theorem expectation_add (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    (hf : Continuous f) (hg : Continuous g) :
    ballExpectation r Ψ (fun η => f η + g η) = ballExpectation r Ψ f + ballExpectation r Ψ g := by
  unfold ballExpectation
  rw [← add_div, ← integral_add (integrable_mul_density hρ hr hΨ hf) (integrable_mul_density hρ hr hΨ hg)]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
theorem expectation_const_mul (c : ℝ) : ballExpectation r Ψ (fun η => c * f η) = c * ballExpectation r Ψ f := by
  unfold ballExpectation
  rw [mul_div_assoc', ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
theorem expectation_one (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ) :
    ballExpectation r Ψ (fun _ => 1) = 1 := by
  unfold ballExpectation
  simp only [one_mul]
  exact div_self (density_integral_pos hρ hr hΨ).ne'
theorem expectation_const (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ) (c : ℝ) :
    ballExpectation r Ψ (fun _ => c) = c := by
  have := expectation_const_mul (r := r) (Ψ := Ψ) (f := fun _ => 1) c
  simpa [expectation_one hρ hr hΨ] using this
theorem expectation_sum {α : Type} (s : Finset α) (F : α → BondField ι → ℝ) (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ) (hF : ∀ a ∈ s, Continuous (F a)) :
    ballExpectation r Ψ (fun η => ∑ a ∈ s, F a η) = ∑ a ∈ s, ballExpectation r Ψ (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expectation_const hρ hr hΨ 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [expectation_add hρ hr hΨ (hF a (Finset.mem_insert_self _ _))
      (continuous_finset_sum _ fun c hc => hF c (Finset.mem_insert_of_mem hc)),
      ih fun c hc => hF c (Finset.mem_insert_of_mem hc)]
theorem expectation_mono (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    (hf : Continuous f) (hg : Continuous g) (h : ∀ η ∈ openPolyball ι ρ, f η ≤ g η) :
    ballExpectation r Ψ f ≤ ballExpectation r Ψ g := by
  unfold ballExpectation
  apply div_le_div_of_nonneg_right _ (density_integral_pos hρ hr hΨ).le
  apply integral_mono (integrable_mul_density hρ hr hΨ hf) (integrable_mul_density hρ hr hΨ hg)
  intro η
  by_cases hη : η ∈ openPolyball ι ρ
  · exact mul_le_mul_of_nonneg_right (h η hη) (nonneg_density hr η)
  · simp [ballDensity, weightProd_eq_zero hr η hη]
theorem abs_expectation_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    (hf : Continuous f) (hg : Continuous g) (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤ g η) :
    |ballExpectation r Ψ f| ≤ ballExpectation r Ψ g := by
  rw [abs_le]
  constructor
  · have := expectation_mono (f := fun η => (-1) * g η) (g := f) hρ hr hΨ (continuous_const.mul hg) hf
      (fun η hη => by have := abs_le.mp (h η hη); linarith [this.1])
    rw [expectation_const_mul] at this
    linarith
  · exact expectation_mono hρ hr hΨ hf hg fun η hη => (le_abs_self _).trans (h η hη)
theorem covariance_add (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    {h : BondField ι → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ballCovariance r Ψ f (fun η => g η + h η) = ballCovariance r Ψ f g + ballCovariance r Ψ f h := by
  unfold ballCovariance
  have e : (fun η => f η * (g η + h η)) = fun η => f η * g η + f η * h η := by
    funext η; ring
  rw [e, expectation_add (f := fun η => f η * g η) (g := fun η => f η * h η) hρ hr hΨ (hf.mul hg) (hf.mul hh),
    expectation_add hρ hr hΨ hg hh]
  ring
theorem covariance_const_mul (c : ℝ) :
    ballCovariance r Ψ f (fun η => c * g η) = c * ballCovariance r Ψ f g := by
  unfold ballCovariance
  have e : (fun η => f η * (c * g η)) = fun η => c * (f η * g η) := by
    funext η; ring
  rw [e, expectation_const_mul, expectation_const_mul]
  ring
theorem covariance_sub (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    {h : BondField ι → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ballCovariance r Ψ f (fun η => g η - h η) = ballCovariance r Ψ f g - ballCovariance r Ψ f h := by
  have := covariance_add (g := g) (h := fun η => (-1) * h η) hρ hr hΨ hf hg (continuous_const.mul hh)
  rw [covariance_const_mul] at this
  simp only [neg_mul, one_mul, ← sub_eq_add_neg] at this
  exact this
theorem covariance_zero : ballCovariance r Ψ f (fun _ => 0) = 0 := by
  have := covariance_const_mul (r := r) (Ψ := Ψ) (f := f) (g := fun _ => 0) 0
  simpa using this
theorem covariance_sum {α : Type} (s : Finset α) (G : α → BondField ι → ℝ) (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ) (hf : Continuous f)
    (hG : ∀ a ∈ s, Continuous (G a)) :
    ballCovariance r Ψ f (fun η => ∑ a ∈ s, G a η) = ∑ a ∈ s, ballCovariance r Ψ f (G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using covariance_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [covariance_add hρ hr hΨ hf (hG a (Finset.mem_insert_self _ _))
      (continuous_finset_sum _ fun c hc => hG c (Finset.mem_insert_of_mem hc)),
      ih fun c hc => hG c (Finset.mem_insert_of_mem hc)]
theorem l2Norm_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hΨ : Continuous Ψ)
    (hf : Continuous f) (hg : Continuous g) (h : ∀ η ∈ openPolyball ι ρ, f η ^ 2 ≤ g η) {c : ℝ}
    (hc : ballExpectation r Ψ g ≤ c ^ 2) (hc0 : 0 ≤ c) : ballL2Norm r Ψ f ≤ c := by
  unfold ballL2Norm
  have := expectation_mono (f := fun η => f η ^ 2) hρ hr hΨ (hf.pow 2) hg h
  exact Real.sqrt_le_iff.mpr ⟨hc0, this.trans hc⟩
end Linear
end Cutoff
section Extension
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι]
def restrictionMap (e : Λ → ι) : BondField ι →L[ℝ] BondField Λ :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) (e l)
def freezeMap (e : Λ → ι) : BondField ι →L[ℝ] BondField ι := (zeroExtensionL e).comp (restrictionMap e)
variable {e : Λ → ι}
theorem zeroExtension_apply_self (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) :
    zeroExtensionL e ζ (e l) = ζ l := by
  have h : ∃ l', e l' = e l := ⟨l, rfl⟩
  have h2 : h.choose = l := he h.choose_spec
  simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_pos h]
  simp [h2]
theorem zeroExtension_apply_off {b : ι} (hb : b ∉ Set.range e) (ζ : BondField Λ) : zeroExtensionL e ζ b = 0 := by
  have h : ¬ ∃ l, e l = b := hb
  simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_neg h]
  simp
@[simp] theorem restrictionMap_apply (η : BondField ι) (l : Λ) : restrictionMap e η l = η (e l) := by
  simp [restrictionMap]
theorem freezeMap_apply_mem (he : Function.Injective e) (η : BondField ι) (l : Λ) :
    freezeMap e η (e l) = η (e l) := by
  simp [freezeMap, zeroExtension_apply_self he]
theorem freezeMap_apply_off {b : ι} (hb : b ∉ Set.range e) (η : BondField ι) : freezeMap e η b = 0 := by
  simp [freezeMap, zeroExtension_apply_off hb]
theorem norm_freezeMap_le (he : Function.Injective e) (η : BondField ι) (b : ι) :
    ‖freezeMap e η b‖ ≤ ‖η b‖ := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hb
    rw [freezeMap_apply_mem he]
  · rw [freezeMap_apply_off hb]; simp
theorem zeroExtension_mem_polyball {ρ : ℝ} (hρ : 0 < ρ) (he : Function.Injective e) {ζ : BondField Λ}
    (h : ζ ∈ openPolyball Λ ρ) : zeroExtensionL e ζ ∈ openPolyball ι ρ := fun b => by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hb
    rw [zeroExtension_apply_self he]
    exact h l
  · rw [zeroExtension_apply_off hb]; simpa using hρ
theorem restrictionMap_mem_polyball {ρ : ℝ} {η : BondField ι} (h : η ∈ openPolyball ι ρ) :
    restrictionMap e η ∈ openPolyball Λ ρ := fun l => by
  rw [restrictionMap_apply]
  exact h _
theorem freezeMap_mem_polyball {ρ : ℝ} (hρ : 0 < ρ) (he : Function.Injective e) {η : BondField ι}
    (h : η ∈ openPolyball ι ρ) : freezeMap e η ∈ openPolyball ι ρ :=
  zeroExtension_mem_polyball hρ he (restrictionMap_mem_polyball h)
theorem zeroExtension_bondVariation (he : Function.Injective e) (l : Λ) (v : BondVector) :
    zeroExtensionL e (bondVariation l v) = bondVariation (e l) v := by
  funext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l', rfl⟩ := hb
    rw [zeroExtension_apply_self he]
    by_cases h : l' = l
    · subst h; simp [bondVariation]
    · have : e l' ≠ e l := fun h' => h (he h')
      simp [bondVariation, h, this]
  · rw [zeroExtension_apply_off hb]
    have : b ≠ e l := fun h => hb ⟨l, h.symm⟩
    simp [bondVariation, this]
theorem freezeMap_bondVariation_mem (he : Function.Injective e) (l : Λ) (v : BondVector) :
    freezeMap e (bondVariation (e l) v) = bondVariation (e l) v := by
  have : restrictionMap e (bondVariation (e l) v) = bondVariation l v := by
    funext l'
    rw [restrictionMap_apply]
    by_cases h : l' = l
    · subst h; simp [bondVariation]
    · have : e l' ≠ e l := fun h' => h (he h')
      simp [bondVariation, h, this]
  simp only [freezeMap, ContinuousLinearMap.comp_apply, this, zeroExtension_bondVariation he]
theorem freezeMap_bondVariation_off {b : ι} (hb : b ∉ Set.range e) (v : BondVector) :
    freezeMap e (bondVariation b v) = 0 := by
  have : restrictionMap e (bondVariation b v) = 0 := by
    funext l
    rw [restrictionMap_apply]
    have : e l ≠ b := fun h => hb ⟨l, h⟩
    simp [bondVariation, this]
  simp [freezeMap, this]
theorem sum_eq_sum_comp_of_vanish (he : Function.Injective e) (G : ι → ℝ) (h : ∀ b, b ∉ Set.range e → G b = 0) :
    ∑ b, G b = ∑ l, G (e l) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := G) (fun a _ b _ hab => he hab)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  apply h
  rintro ⟨l, rfl⟩
  exact hb (Finset.mem_image_of_mem _ (Finset.mem_univ _))
theorem sum_comp_le_sum_of_nonneg (he : Function.Injective e) (G : ι → ℝ) (h : ∀ b, 0 ≤ G b) :
    ∑ l, G (e l) ≤ ∑ b, G b := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := G) (fun a _ b _ hab => he hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => h b
end Extension
section Chain
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem fderiv_comp_linearMap (L : BondField α →L[ℝ] BondField β) {g : BondField β → ℝ}
    {η : BondField α} (hg : DifferentiableAt ℝ g (L η)) :
    fderiv ℝ (fun ζ => g (L ζ)) η = (fderiv ℝ g (L η)).comp L :=
  (hg.hasFDerivAt.comp η L.hasFDerivAt).fderiv
theorem differentiable_fderiv_apply_const {Ψ : BondField β → ℝ} (hΨ : ContDiff ℝ 2 Ψ) (u : BondField β) :
    Differentiable ℝ (fun ζ => fderiv ℝ Ψ ζ u) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  exact (h1.differentiable (by simp)).clm_apply (differentiable_const u)
theorem secondDeriv_comp_linearMap (L : BondField α →L[ℝ] BondField β) {Ψ : BondField β → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (η u v : BondField α) :
    secondDerivAlong (fun ζ => Ψ (L ζ)) η u v = secondDerivAlong Ψ (L η) (L u) (L v) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  unfold secondDerivAlong
  have : (fun ζ => fderiv ℝ (fun ζ => Ψ (L ζ)) ζ u) = fun ζ => fderiv ℝ Ψ (L ζ) (L u) := by
    funext ζ
    rw [fderiv_comp_linearMap L (hd _)]
    rfl
  rw [this, fderiv_comp_linearMap L (g := fun z => fderiv ℝ Ψ z (L u)) (differentiable_fderiv_apply_const hΨ _ _)]
  rfl
theorem bondPartial_comp_linearMap (L : BondField α →L[ℝ] BondField β) {Ψ : BondField β → ℝ}
    (hΨ : Differentiable ℝ Ψ) (b : α) (η : BondField α) (v : BondVector) :
    bondPartialDeriv (fun ζ => Ψ (L ζ)) b η v = fderiv ℝ Ψ (L η) (L (bondVariation b v)) := by
  unfold bondPartialDeriv
  rw [fderiv_comp_linearMap L (hΨ _)]
  rfl
end Chain
section Convexity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ} {d : ι → ι → ℝ}
theorem kernel_entry_nonneg {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} (hρ : 0 < ρ)
    (h : IsUniformlyConvexDecaying ρ m κ d Ψ K) (b b' : ι) : 0 ≤ K b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.kernel_nonneg <;> assumption
theorem pseudoMetric_apply_nonneg (hd : IsPseudoMetricOnBonds d) (b b' : ι) : 0 ≤ d b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.pseudoMetric_nonneg <;> assumption
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsConvexWithSmallGradient.contDiff_three {Ψ : BondField ι → ℝ} (h : IsConvexWithSmallGradient ρ m κ d Ψ) : ContDiff ℝ 3 Ψ := by
  obtain ⟨⟨K, hK⟩, _⟩ := h
  exact hK.smooth
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsConvexWithSmallGradient.continuous_potential {Ψ : BondField ι → ℝ} (h : IsConvexWithSmallGradient ρ m κ d Ψ) : Continuous Ψ :=
  h.contDiff_three.continuous
theorem secondDeriv_segment {A B : BondField ι → ℝ} (hA : ContDiff ℝ 3 A) (hB : ContDiff ℝ 3 B)
    (v : ℝ) (η u w : BondField ι) :
    secondDerivAlong (segmentInterpolant A B v) η u w = v * secondDerivAlong B η u w + (1 - v) * secondDerivAlong A η u w := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B := hB.of_le (by norm_num)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  have hBd : Differentiable ℝ B := hB.differentiable (by simp)
  have h1 : (fun ζ => fderiv ℝ (segmentInterpolant A B v) ζ u) =
      fun ζ => v * fderiv ℝ B ζ u + (1 - v) * fderiv ℝ A ζ u := by
    funext ζ
    have : HasFDerivAt (segmentInterpolant A B v) (v • fderiv ℝ B ζ + (1 - v) • fderiv ℝ A ζ) ζ :=
      ((hBd ζ).hasFDerivAt.const_mul v).add ((hAd ζ).hasFDerivAt.const_mul (1 - v))
    rw [this.fderiv]
    simp
  unfold secondDerivAlong
  rw [h1]
  have : HasFDerivAt (fun ζ => v * fderiv ℝ B ζ u + (1 - v) * fderiv ℝ A ζ u)
      (v • fderiv ℝ (fun ζ => fderiv ℝ B ζ u) η + (1 - v) • fderiv ℝ (fun ζ => fderiv ℝ A ζ u) η) η :=
    ((differentiable_fderiv_apply_const hB2 u η).hasFDerivAt.const_mul v).add
      ((differentiable_fderiv_apply_const hA2 u η).hasFDerivAt.const_mul (1 - v))
  rw [this.fderiv]
  simp
theorem segment_contDiff {A B : BondField ι → ℝ} (hA : ContDiff ℝ 3 A) (hB : ContDiff ℝ 3 B)
    (v : ℝ) : ContDiff ℝ 3 (segmentInterpolant A B v) :=
  (contDiff_const.mul hB).add (contDiff_const.mul hA)
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsConvexWithSmallGradient.interpolate {A B : BondField ι → ℝ} (hm : 0 < m) (hA : IsConvexWithSmallGradient ρ m κ d A)
    (hB : IsConvexWithSmallGradient ρ m κ d B) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    IsConvexWithSmallGradient ρ m κ d (segmentInterpolant A B v) := by
  obtain ⟨⟨KA, hKA⟩, sA⟩ := hA
  obtain ⟨⟨KB, hKB⟩, sB⟩ := hB
  have h1' : 0 ≤ 1 - v := by linarith
  refine ⟨⟨fun b b' => v * KB b b' + (1 - v) * KA b b', ?_⟩, ?_⟩
  · refine ⟨segment_contDiff hKA.smooth hKB.smooth v, ?_, ?_, ?_, ?_⟩
    · intro η hη u
      rw [secondDeriv_segment hKA.smooth hKB.smooth]
      have e1 := hKA.floor η hη u
      have e2 := hKB.floor η hη u
      nlinarith [mul_le_mul_of_nonneg_left e2 h0, mul_le_mul_of_nonneg_left e1 h1']
    · intro η hη b b' x y
      rw [secondDeriv_segment hKA.smooth hKB.smooth]
      have e1 := hKA.kernel η hη b b' x y
      have e2 := hKB.kernel η hη b b' x y
      calc _ ≤ |v * secondDerivAlong B η (bondVariation b x) (bondVariation b' y)| +
            |(1 - v) * secondDerivAlong A η (bondVariation b x) (bondVariation b' y)| := abs_add_le _ _
        _ = v * |secondDerivAlong B η (bondVariation b x) (bondVariation b' y)| +
            (1 - v) * |secondDerivAlong A η (bondVariation b x) (bondVariation b' y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1']
        _ ≤ v * (KB b b' * ‖x‖ * ‖y‖) + (1 - v) * (KA b b' * ‖x‖ * ‖y‖) := by gcongr
        _ = _ := by ring
    · intro b b'
      simp only [hKA.symm b b', hKB.symm b b']
    · intro b
      have e1 := hKA.standingConstraints b
      have e2 := hKB.standingConstraints b
      have : ∑ b', (v * KB b b' + (1 - v) * KA b b') * (Real.exp (2 * κ * d b b') - 1) =
          v * ∑ b', KB b b' * (Real.exp (2 * κ * d b b') - 1) +
            (1 - v) * ∑ b', KA b b' * (Real.exp (2 * κ * d b b') - 1) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left e2 h0, mul_le_mul_of_nonneg_left e1 h1']
  · intro b x
    have hAd : Differentiable ℝ A := hKA.smooth.differentiable (by simp)
    have hBd : Differentiable ℝ B := hKB.smooth.differentiable (by simp)
    have : bondPartialDeriv (segmentInterpolant A B v) b 0 x = v * bondPartialDeriv B b 0 x + (1 - v) * bondPartialDeriv A b 0 x := by
      unfold bondPartialDeriv
      have : HasFDerivAt (segmentInterpolant A B v) (v • fderiv ℝ B 0 + (1 - v) • fderiv ℝ A 0) 0 :=
        ((hBd 0).hasFDerivAt.const_mul v).add ((hAd 0).hasFDerivAt.const_mul (1 - v))
      rw [this.fderiv]
      simp
    rw [this]
    calc _ ≤ |v * bondPartialDeriv B b 0 x| + |(1 - v) * bondPartialDeriv A b 0 x| := abs_add_le _ _
      _ = v * |bondPartialDeriv B b 0 x| + (1 - v) * |bondPartialDeriv A b 0 x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1']
      _ ≤ v * (Real.sqrt m * ‖x‖) + (1 - v) * (Real.sqrt m * ‖x‖) := by
        gcongr
        · exact sB b x
        · exact sA b x
      _ = _ := by ring
end Convexity
section Pullback
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ}
  {d : ι → ι → ℝ} {e : Λ → ι}
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsConvexWithSmallGradient.pullback {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (he : Function.Injective e) (hd : IsPseudoMetricOnBonds d)
    (h : IsConvexWithSmallGradient ρ m κ d Ψ) :
    IsConvexWithSmallGradient ρ m κ (fun l l' => d (e l) (e l')) (fun ζ => Ψ (zeroExtensionL e ζ)) := by
  obtain ⟨⟨K, hK⟩, s⟩ := h
  have hΨ2 : ContDiff ℝ 2 Ψ := hK.smooth.of_le (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hK.smooth.differentiable (by simp)
  refine ⟨⟨fun l l' => K (e l) (e l'), ?_⟩, ?_⟩
  · refine ⟨hK.smooth.comp (zeroExtensionL e).contDiff, ?_, ?_, ?_, ?_⟩
    · intro ζ hζ u
      rw [secondDeriv_comp_linearMap _ hΨ2]
      have h1 := hK.floor (zeroExtensionL e ζ) (zeroExtension_mem_polyball hρ he hζ) (zeroExtensionL e u)
      have h2 : ∑ b, ‖zeroExtensionL e u b‖ ^ 2 = ∑ l, ‖u l‖ ^ 2 := by
        rw [sum_eq_sum_comp_of_vanish he _ (fun b hb => by rw [zeroExtension_apply_off hb]; simp)]
        exact Finset.sum_congr rfl fun l _ => by rw [zeroExtension_apply_self he]
      rwa [h2] at h1
    · intro ζ hζ l l' x y
      rw [secondDeriv_comp_linearMap _ hΨ2, zeroExtension_bondVariation he, zeroExtension_bondVariation he]
      exact hK.kernel _ (zeroExtension_mem_polyball hρ he hζ) _ _ x y
    · intro l l'
      exact hK.symm _ _
    · intro l
      refine le_trans ?_ (hK.standingConstraints (e l))
      refine sum_comp_le_sum_of_nonneg he (fun b' => K (e l) b' * (Real.exp (2 * κ * d (e l) b') - 1)) fun b' => ?_
      refine mul_nonneg (kernel_entry_nonneg hρ hK _ _) ?_
      have : 0 ≤ 2 * κ * d (e l) b' := mul_nonneg (by linarith) (pseudoMetric_apply_nonneg hd _ _)
      linarith [Real.add_one_le_exp (2 * κ * d (e l) b')]
  · intro l x
    rw [bondPartial_comp_linearMap _ hΨd, zeroExtension_bondVariation he, map_zero]
    exact s _ x
end Pullback
section OffBonds
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ}
  {d : ι → ι → ℝ} {e : Λ → ι}
open Classical in
def offBonds (e : Λ → ι) : Finset ι := Finset.univ.filter fun b => b ∉ Set.range e
def offBondsSq (e : Λ → ι) (c : ℝ) (η : BondField ι) : ℝ := c * ∑ b ∈ offBonds e, ‖η b‖ ^ 2
theorem mem_offBonds {b : ι} : b ∈ offBonds e ↔ b ∉ Set.range e := by simp [offBonds]
def pairingMap (S : Finset ι) (u : BondField ι) : BondField ι →L[ℝ] ℝ :=
  ∑ b ∈ S, (innerSL ℝ (u b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)
theorem pairingMap_apply (S : Finset ι) (u v : BondField ι) : pairingMap S u v = ∑ b ∈ S, ⟪u b, v b⟫ := by
  simp [pairingMap, ContinuousLinearMap.sum_apply]
theorem offBondsSq_hasFDerivAt (c : ℝ) (η : BondField ι) :
    HasFDerivAt (offBondsSq e c) ((2 * c) • pairingMap (offBonds e) η) η := by
  have h1 : ∀ b, HasFDerivAt (fun ζ : BondField ι => ‖ζ b‖ ^ 2)
      ((2 : ℝ) • (innerSL ℝ (η b)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)) η := fun b => by
    have := (hasStrictFDerivAt_norm_sq (η b)).hasFDerivAt.comp η
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b).hasFDerivAt
    refine HasFDerivAt.congr_fderiv this ?_
    ext v
    simp
  have h2 := (HasFDerivAt.fun_sum (u := offBonds e) fun b _ => h1 b).const_mul c
  refine HasFDerivAt.congr_fderiv h2 ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, pairingMap_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring
theorem offBondsSq_contDiff (c : ℝ) : ContDiff ℝ 3 (offBondsSq e c) := by
  unfold offBondsSq
  apply contDiff_const.mul
  apply ContDiff.sum
  intro b _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ BondVector b)
theorem offBondsSq_secondDeriv (c : ℝ) (η u v : BondField ι) :
    secondDerivAlong (offBondsSq e c) η u v = 2 * c * ∑ b ∈ offBonds e, ⟪u b, v b⟫ := by
  unfold secondDerivAlong
  have h : (fun ζ => fderiv ℝ (offBondsSq e c) ζ u) = fun ζ => ((2 * c) • pairingMap (offBonds e) u) ζ := by
    funext ζ
    rw [(offBondsSq_hasFDerivAt c ζ).fderiv]
    simp only [ContinuousLinearMap.smul_apply, pairingMap_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
  rw [h, ContinuousLinearMap.fderiv]
  simp [pairingMap_apply]
theorem secondDeriv_add {A B : BondField ι → ℝ} (hA : ContDiff ℝ 3 A) (hB : ContDiff ℝ 3 B)
    (η u w : BondField ι) :
    secondDerivAlong (fun ζ => A ζ + B ζ) η u w = secondDerivAlong A η u w + secondDerivAlong B η u w := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_add <;> assumption
theorem secondDeriv_zero_dir {Ψ : BondField ι → ℝ} (η w : BondField ι) :
    secondDerivAlong Ψ η 0 w = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.secondDerivAlong_zero_left <;> assumption
theorem sum_inner_bondVariation_eq (S : Finset ι) (b b' : ι) (x y : BondVector) :
    ∑ c ∈ S, ⟪bondVariation b x c, bondVariation b' y c⟫ = if b ∈ S ∧ b = b' then ⟪x, y⟫ else 0 := by
  by_cases h : b ∈ S ∧ b = b'
  · obtain ⟨hb, rfl⟩ := h
    rw [if_pos ⟨hb, rfl⟩, Finset.sum_eq_single b]
    · simp [bondVariation]
    · intro c _ hc
      simp [bondVariation, hc]
    · exact fun h' => absurd hb h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c hc
    by_cases h1 : c = b
    · subst h1
      have : c ≠ b' := fun h' => h ⟨hc, h'⟩
      simp [bondVariation, this]
    · simp [bondVariation, h1]
def frozenPotential (Ψ : BondField ι → ℝ) (e : Λ → ι) (c : ℝ) (η : BondField ι) : ℝ :=
  Ψ (freezeMap e η) + offBondsSq e c η
theorem frozenPotential_secondDeriv {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (c : ℝ)
    (η u v : BondField ι) :
    secondDerivAlong (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e c) η u v = secondDerivAlong Ψ (freezeMap e η) (freezeMap e u) (freezeMap e v) +
      2 * c * ∑ b ∈ offBonds e, ⟪u b, v b⟫ := by
  have h1 : ContDiff ℝ 3 fun ζ => Ψ (freezeMap e ζ) := hΨ.comp (freezeMap e).contDiff
  have := secondDeriv_add h1 (offBondsSq_contDiff (e := e) c) η u v
  rw [offBondsSq_secondDeriv, secondDeriv_comp_linearMap _ (hΨ.of_le (by norm_num))] at this
  exact this
open Classical in
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsConvexWithSmallGradient.freeze {Ψ : BondField ι → ℝ} {c : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hm : 0 < m)
    (hc : m ≤ c) (he : Function.Injective e) (hd : IsPseudoMetricOnBonds d)
    (h : IsConvexWithSmallGradient ρ m κ d Ψ) : IsConvexWithSmallGradient ρ m κ d (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e c) := by
  obtain ⟨⟨K, hK⟩, s⟩ := h
  have hΨd : Differentiable ℝ Ψ := hK.smooth.differentiable (by simp)
  have hc0 : 0 ≤ c := hm.le.trans hc
  refine ⟨⟨fun b b' => if b ∈ Set.range e ∧ b' ∈ Set.range e then K b b'
      else if b = b' then 2 * c else 0, ?_⟩, ?_⟩
  · refine ⟨(hK.smooth.comp (freezeMap e).contDiff).add (offBondsSq_contDiff c), ?_, ?_, ?_, ?_⟩
    · intro η hη u
      rw [frozenPotential_secondDeriv hK.smooth]
      have h1 := hK.floor _ (freezeMap_mem_polyball hρ he hη) (freezeMap e u)
      have h2 : ∑ b, ‖u b‖ ^ 2 = ∑ b, ‖freezeMap e u b‖ ^ 2 + ∑ b ∈ offBonds e, ‖u b‖ ^ 2 := by
        rw [offBonds, Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : b ∈ Set.range e
        · obtain ⟨l, rfl⟩ := hb
          simp [freezeMap_apply_mem he]
        · simp [freezeMap_apply_off hb, hb]
      have h3 : ∑ b ∈ offBonds e, ⟪u b, u b⟫ = ∑ b ∈ offBonds e, ‖u b‖ ^ 2 :=
        Finset.sum_congr rfl fun b _ => real_inner_self_eq_norm_sq _
      have h4 : 0 ≤ ∑ b ∈ offBonds e, ‖u b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
      rw [h2, h3]
      nlinarith [mul_le_mul_of_nonneg_right hc h4]
    · intro η hη b b' x y
      rw [frozenPotential_secondDeriv hK.smooth, sum_inner_bondVariation_eq]
      by_cases hb : b ∈ Set.range e
      · by_cases hb' : b' ∈ Set.range e
        · obtain ⟨l, rfl⟩ := hb
          obtain ⟨l', rfl⟩ := hb'
          have hA : ¬(e l ∈ offBonds e ∧ e l = e l') := fun h => mem_offBonds.mp h.1 ⟨l, rfl⟩
          have hB : e l ∈ Set.range e ∧ e l' ∈ Set.range e := ⟨⟨l, rfl⟩, ⟨l', rfl⟩⟩
          rw [freezeMap_bondVariation_mem he, freezeMap_bondVariation_mem he, if_neg hA, if_pos hB]
          simpa using hK.kernel _ (freezeMap_mem_polyball hρ he hη) _ _ x y
        · have hne : b ≠ b' := fun h => hb' (h ▸ hb)
          have hA : ¬(b ∈ offBonds e ∧ b = b') := fun h => hne h.2
          have hB : ¬(b ∈ Set.range e ∧ b' ∈ Set.range e) := fun h => hb' h.2
          rw [freezeMap_bondVariation_off hb', if_neg hA, if_neg hB, if_neg hne]
          simp [secondDerivAlong]
      · have hB : ¬(b ∈ Set.range e ∧ b' ∈ Set.range e) := fun h => hb h.1
        rw [freezeMap_bondVariation_off hb, secondDeriv_zero_dir, if_neg hB]
        by_cases hbb : b = b'
        · subst hbb
          have hA : b ∈ offBonds e ∧ b = b := ⟨mem_offBonds.mpr hb, rfl⟩
          rw [if_pos hA, if_pos rfl, zero_add, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * c)]
          have := abs_real_inner_le_norm x y
          calc 2 * c * |⟪x, y⟫| ≤ 2 * c * (‖x‖ * ‖y‖) := by gcongr
            _ = _ := by ring
        · have hA : ¬(b ∈ offBonds e ∧ b = b') := fun h => hbb h.2
          rw [if_neg hbb, if_neg hA]
          simp
    · intro b b'
      simp only [hK.symm b b', and_comm, eq_comm]
    · intro b
      by_cases hb : b ∈ Set.range e
      · refine le_trans (Finset.sum_le_sum fun b' _ => ?_) (hK.standingConstraints b)
        have hx : 0 ≤ Real.exp (2 * κ * d b b') - 1 := by
          have : 0 ≤ 2 * κ * d b b' := mul_nonneg (by linarith) (pseudoMetric_apply_nonneg hd _ _)
          linarith [Real.add_one_le_exp (2 * κ * d b b')]
        by_cases hb' : b' ∈ Set.range e
        · rw [if_pos ⟨hb, hb'⟩]
        · have hne : b ≠ b' := fun h => hb' (h ▸ hb)
          rw [if_neg (fun h => hb' h.2), if_neg hne, zero_mul]
          exact mul_nonneg (kernel_entry_nonneg hρ hK _ _) hx
      · have : ∀ b', (if b ∈ Set.range e ∧ b' ∈ Set.range e then K b b'
            else if b = b' then 2 * c else 0) * (Real.exp (2 * κ * d b b') - 1) = 0 := fun b' => by
          rw [if_neg (fun h => hb h.1)]
          by_cases hbb : b = b'
          · subst hbb
            simp [hd.self]
          · simp [hbb]
        simp only [this, Finset.sum_const_zero]
        exact hm.le
  · intro b x
    have hp : bondPartialDeriv (ValueFreezing.frozenPotential Ψ e c) b 0 x =
        fderiv ℝ Ψ 0 (freezeMap e (bondVariation b x)) := by
      unfold bondPartialDeriv
      have h1 : HasFDerivAt (ValueFreezing.frozenPotential Ψ e c)
          (((fderiv ℝ Ψ (freezeMap e 0)).comp (freezeMap e)) + (2 * c) • pairingMap (offBonds e) 0) 0 :=
        ((hΨd _).hasFDerivAt.comp 0 (freezeMap e).hasFDerivAt).add (offBondsSq_hasFDerivAt c 0)
      rw [h1.fderiv]
      simp [pairingMap_apply]
    rw [hp]
    by_cases hb : b ∈ Set.range e
    · obtain ⟨l, rfl⟩ := hb
      rw [freezeMap_bondVariation_mem he]
      exact s _ x
    · rw [freezeMap_bondVariation_off hb]
      simp
      positivity
end OffBonds
section Marginal
variable {Λ ι : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] {ρ : ℝ} {r : ℝ → ℝ}
  {e : Λ → ι}
abbrev OffBond (e : Λ → ι) : Type := {b : ι // b ∉ Set.range e}
instance offBondFintype (e : Λ → ι) : Fintype (OffBond e) := Fintype.ofFinite _
instance offBondDecEq (e : Λ → ι) : DecidableEq (OffBond e) := Classical.decEq _
def bondSplit (he : Function.Injective e) : Λ ⊕ OffBond e ≃ ι :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · have : a = b := he h
        rw [this]
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · have : a = b := Subtype.ext h
        rw [this]
    · intro b
      by_cases hb : b ∈ Set.range e
      · obtain ⟨l, rfl⟩ := hb
        exact ⟨Sum.inl l, rfl⟩
      · exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩)
def joinFields (he : Function.Injective e) :
    BondField Λ × BondField (OffBond e) ≃ᵐ BondField ι :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Λ ⊕ OffBond e => BondVector)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ι => BondVector) (bondSplit he))
theorem joinFields_measurePreserving (he : Function.Injective e) : MeasurePreserving (joinFields he) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Λ ⊕ OffBond e => BondVector)).symm.trans
    (volume_measurePreserving_piCongrLeft (fun _ : ι => BondVector) (bondSplit he))
theorem joinFields_apply_mem (he : Function.Injective e) (z : BondField Λ × BondField (OffBond e)) (l : Λ) :
    joinFields he z (e l) = z.1 l := by
  have : e l = bondSplit he (Sum.inl l) := rfl
  rw [this]
  simp only [joinFields, MeasurableEquiv.trans_apply]
  erw [Equiv.piCongrLeft_apply_apply]
  rfl
theorem joinFields_apply_off (he : Function.Injective e) (z : BondField Λ × BondField (OffBond e))
    (o : OffBond e) : joinFields he z o.1 = z.2 o := by
  have : o.1 = bondSplit he (Sum.inr o) := rfl
  rw [this]
  simp only [joinFields, MeasurableEquiv.trans_apply]
  erw [Equiv.piCongrLeft_apply_apply]
  rfl
theorem restrictionMap_joinFields (he : Function.Injective e) (z : BondField Λ × BondField (OffBond e)) :
    restrictionMap e (joinFields he z) = z.1 := by
  funext l
  rw [restrictionMap_apply, joinFields_apply_mem]
theorem weightProd_joinFields (he : Function.Injective e) (z : BondField Λ × BondField (OffBond e)) :
    radialWeightProd r (joinFields he z) = radialWeightProd r z.1 * radialWeightProd r z.2 := by
  unfold radialWeightProd
  rw [← Equiv.prod_comp (bondSplit he), Fintype.prod_sum_type]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by
      change r ‖joinFields he z (e l)‖ = _
      rw [joinFields_apply_mem]
  · exact Finset.prod_congr rfl fun o _ => by
      change r ‖joinFields he z o.1‖ = _
      rw [joinFields_apply_off]
theorem offBonds_sum_joinFields (he : Function.Injective e) (z : BondField Λ × BondField (OffBond e)) :
    ∑ b ∈ offBonds e, ‖joinFields he z b‖ ^ 2 = ∑ o, ‖z.2 o‖ ^ 2 := by
  classical
  have : offBonds e = Finset.univ.map (Function.Embedding.subtype (fun b => b ∉ Set.range e)) := by
    ext b
    simp [mem_offBonds]
  rw [this, Finset.sum_map]
  exact Finset.sum_congr rfl fun o _ => by
    change ‖joinFields he z o.1‖ ^ 2 = _
    rw [joinFields_apply_off]
theorem integral_frozen_factor (he : Function.Injective e) (G h : BondField Λ → ℝ) (c : ℝ) :
    ∫ η, h (restrictionMap e η) * ballDensity r
        (fun η => G (restrictionMap e η) + offBondsSq e c η) η =
      (∫ ζ, h ζ * ballDensity r G ζ) *
        ∫ ξ, ballDensity r (fun ξ : BondField (OffBond e) => c * ∑ o, ‖ξ o‖ ^ 2) ξ := by
  classical
  rw [← (joinFields_measurePreserving he).integral_comp']
  have : ∀ z : BondField Λ × BondField (OffBond e),
      h (restrictionMap e (joinFields he z)) * ballDensity r
        (fun η => G (restrictionMap e η) + offBondsSq e c η) (joinFields he z) =
      (h z.1 * ballDensity r G z.1) *
        ballDensity r (fun ξ : BondField (OffBond e) => c * ∑ o, ‖ξ o‖ ^ 2) z.2 := fun z => by
    simp only [ballDensity, restrictionMap_joinFields, weightProd_joinFields, offBondsSq, offBonds_sum_joinFields]
    rw [neg_add, Real.exp_add]
    ring
  simp_rw [this]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (L := ℝ) (fun ζ => h ζ * ballDensity r G ζ) _
theorem expectation_frozen (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (he : Function.Injective e)
    {G h : BondField Λ → ℝ} (c : ℝ) :
    ballExpectation r (fun η => G (restrictionMap e η) + offBondsSq e c η) (fun η => h (restrictionMap e η)) =
      ballExpectation r G h := by
  classical
  have hJ : 0 < ∫ ξ, ballDensity r (fun ξ : BondField (OffBond e) => c * ∑ o, ‖ξ o‖ ^ 2) ξ := by
    apply density_integral_pos hρ hr
    exact continuous_const.mul (continuous_finset_sum _ fun o _ => by fun_prop)
  unfold ballExpectation
  have h1 := integral_frozen_factor (r := r) he G h c
  have h2 := integral_frozen_factor (r := r) he G (fun _ => 1) c
  simp only [one_mul] at h2
  rw [h1, h2, mul_div_mul_right _ _ hJ.ne']
end Marginal
def CovarianceBoundHolds (ρ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ), 0 < m → 0 ≤ κ → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ K → ∀ f g : BondField ι → ℝ, ContDiff ℝ 1 f → ContDiff ℝ 1 g →
      |ballCovariance r Ψ f g| ≤ m⁻¹ * ∑ b, ∑ b',
        ballL2Norm r Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
          ballL2Norm r Ψ (bondGradNorm g b')
section Gradients
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem continuous_gradNorm {g : BondField ι → ℝ} (hg : ContDiff ℝ 1 g) (b : ι) :
    Continuous (bondGradNorm g b) := by
  unfold bondGradNorm
  exact ((hg.continuous_fderiv (by simp)).clm_comp continuous_const).norm
theorem gradNorm_nonneg (g : BondField ι → ℝ) (b : ι) (η : BondField ι) :
    0 ≤ bondGradNorm g b η := norm_nonneg _
theorem abs_fderiv_bondVariation_le_gradNorm (g : BondField ι → ℝ) (b : ι) (η : BondField ι) (w : BondVector) :
    |fderiv ℝ g η (bondVariation b w)| ≤ bondGradNorm g b η * ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.abs_fderiv_bondVariation_le <;> assumption
theorem gradNorm_le_of_bound {g : BondField ι → ℝ} {b : ι} {η : BondField ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ w, |fderiv ℝ g η (bondVariation b w)| ≤ B * ‖w‖) : bondGradNorm g b η ≤ B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.bondGradNorm_le_of_forall <;> assumption
variable {Λ : Type} [Fintype Λ] [DecidableEq Λ] {e : Λ → ι}
theorem gradNorm_zeroExtension (he : Function.Injective e) {g : BondField ι → ℝ}
    (hg : Differentiable ℝ g) (l : Λ) (ζ : BondField Λ) :
    bondGradNorm (fun ζ => g (zeroExtensionL e ζ)) l ζ = bondGradNorm g (e l) (zeroExtensionL e ζ) := by
  apply le_antisymm
  · apply gradNorm_le_of_bound (gradNorm_nonneg _ _ _)
    intro w
    rw [fderiv_comp_linearMap _ (hg _), ContinuousLinearMap.comp_apply, zeroExtension_bondVariation he]
    exact abs_fderiv_bondVariation_le_gradNorm _ _ _ _
  · apply gradNorm_le_of_bound (gradNorm_nonneg _ _ _)
    intro w
    have h := abs_fderiv_bondVariation_le_gradNorm (fun ζ => g (zeroExtensionL e ζ)) l ζ w
    rwa [fderiv_comp_linearMap _ (hg _), ContinuousLinearMap.comp_apply, zeroExtension_bondVariation he] at h
theorem gradNorm_freeze_mem_le (he : Function.Injective e) {g : BondField ι → ℝ}
    (hg : Differentiable ℝ g) (l : Λ) (η : BondField ι) :
    bondGradNorm (fun ζ => g (freezeMap e ζ)) (e l) η ≤ bondGradNorm g (e l) (freezeMap e η) := by
  apply gradNorm_le_of_bound (gradNorm_nonneg _ _ _)
  intro w
  rw [fderiv_comp_linearMap _ (hg _), ContinuousLinearMap.comp_apply, freezeMap_bondVariation_mem he]
  exact abs_fderiv_bondVariation_le_gradNorm _ _ _ _
theorem gradNorm_freeze_off {g : BondField ι → ℝ} (hg : Differentiable ℝ g) {b : ι}
    (hb : b ∉ Set.range e) (η : BondField ι) :
    bondGradNorm (fun ζ => g (freezeMap e ζ)) b η = 0 := by
  apply le_antisymm _ (gradNorm_nonneg _ _ _)
  apply gradNorm_le_of_bound le_rfl
  intro w
  rw [fderiv_comp_linearMap _ (hg _), ContinuousLinearMap.comp_apply, freezeMap_bondVariation_off hb]
  simp
theorem gradNorm_sub_le {f g : BondField ι → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (b : ι) (η : BondField ι) :
    bondGradNorm (fun ζ => f ζ - g ζ) b η ≤ bondGradNorm f b η + bondGradNorm g b η := by
  apply gradNorm_le_of_bound (add_nonneg (gradNorm_nonneg _ _ _) (gradNorm_nonneg _ _ _))
  intro w
  have h : HasFDerivAt (fun ζ => f ζ - g ζ) (fderiv ℝ f η - fderiv ℝ g η) η :=
    (hf η).hasFDerivAt.sub (hg η).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.sub_apply, add_mul]
  exact (abs_sub _ _).trans (add_le_add (abs_fderiv_bondVariation_le_gradNorm _ _ _ _) (abs_fderiv_bondVariation_le_gradNorm _ _ _ _))
theorem gradNorm_segment_le {f g : BondField ι → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (b : ι) (η : BondField ι) {B : ℝ}
    (hfB : bondGradNorm f b η ≤ B) (hgB : bondGradNorm g b η ≤ B) :
    bondGradNorm (segmentInterpolant f g v) b η ≤ B := by
  have hB : 0 ≤ B := (gradNorm_nonneg _ _ _).trans hfB
  apply gradNorm_le_of_bound hB
  intro w
  have h : HasFDerivAt (segmentInterpolant f g v) (v • fderiv ℝ g η + (1 - v) • fderiv ℝ f η) η :=
    ((hg η).hasFDerivAt.const_mul v).add ((hf η).hasFDerivAt.const_mul (1 - v))
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h1' : 0 ≤ 1 - v := by linarith
  have e1 := (abs_fderiv_bondVariation_le_gradNorm g b η w).trans (mul_le_mul_of_nonneg_right hgB (norm_nonneg w))
  have e2 := (abs_fderiv_bondVariation_le_gradNorm f b η w).trans (mul_le_mul_of_nonneg_right hfB (norm_nonneg w))
  calc _ ≤ |v * fderiv ℝ g η (bondVariation b w)| + |(1 - v) * fderiv ℝ f η (bondVariation b w)| := abs_add_le _ _
    _ = v * |fderiv ℝ g η (bondVariation b w)| + (1 - v) * |fderiv ℝ f η (bondVariation b w)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1']
    _ ≤ v * (B * ‖w‖) + (1 - v) * (B * ‖w‖) := by gcongr
    _ = _ := by ring
theorem sub_freezeMap_eq_sum (he : Function.Injective e) (η : BondField ι) :
    η - freezeMap e η = ∑ c ∈ offBonds e, bondVariation c (η c) := by
  funext b
  rw [Finset.sum_apply]
  simp only [Pi.sub_apply, bondVariation, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  by_cases hb : b ∈ Set.range e
  · have : b ∉ offBonds e := fun h => mem_offBonds.mp h hb
    obtain ⟨l, rfl⟩ := hb
    rw [if_neg this, freezeMap_apply_mem he, sub_self]
  · rw [if_pos (mem_offBonds.mpr hb), freezeMap_apply_off hb, sub_zero]
def freezePath (e : Λ → ι) (η : BondField ι) (s : ℝ) : BondField ι :=
  freezeMap e η + s • (η - freezeMap e η)
theorem norm_freezePath_le (he : Function.Injective e) (η : BondField ι) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ 1) (b : ι) : ‖freezePath e η s b‖ ≤ ‖η b‖ := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hb
    simp [freezePath, freezeMap_apply_mem he]
  · simp only [freezePath, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, freezeMap_apply_off hb, sub_zero, zero_add,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
theorem freezePath_mem {ρ : ℝ} (he : Function.Injective e) {η : BondField ι} (hη : η ∈ openPolyball ι ρ)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : freezePath e η s ∈ openPolyball ι ρ := fun b =>
  (norm_freezePath_le he η h0 h1 b).trans_lt (hη b)
theorem freezePath_hasDerivAt (η : BondField ι) (s : ℝ) :
    HasDerivAt (freezePath e η) (η - freezeMap e η) s := by
  unfold freezePath
  simpa using ((hasDerivAt_id s).smul_const (η - freezeMap e η)).const_add (freezeMap e η)
theorem abs_sub_freeze_le {g : BondField ι → ℝ} (hg : Differentiable ℝ g) {ρ : ℝ}
    (he : Function.Injective e) {η : BondField ι} {B : ℝ}
    (hB : ∀ s, 0 ≤ s → s ≤ 1 → |fderiv ℝ g (freezePath e η s) (η - freezeMap e η)| ≤ B) :
    |g η - g (freezeMap e η)| ≤ B := by
  have h1 : freezePath e η 1 = η := by simp [freezePath]
  have h0 : freezePath e η 0 = freezeMap e η := by simp [freezePath]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => g (freezePath e η s))
    (f' := fun s => fderiv ℝ g (freezePath e η s) (η - freezeMap e η)) (s := Set.Icc (0 : ℝ) 1) (C := B)
    (x := 0) (y := 1)
    (fun s _ => (((hg _).hasFDerivAt.comp_hasDerivAt s (freezePath_hasDerivAt η s))).hasDerivWithinAt)
    (fun s hs => hB s hs.1 hs.2) (convex_Icc 0 1) (by simp) (by simp)
  simpa [h1, h0] using this
end Gradients
section Sizes
variable {ι 𝒞 : Type} [Fintype ι] [DecidableEq ι] [Fintype 𝒞] [DecidableEq 𝒞]
  {ρ κ S lam x : ℝ} {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ}
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.dist_nonneg (h : IsDecayingPlacement κ S pl D) (Z Z' : 𝒞) : 0 ≤ D Z Z' := by
  have h1 := h.triangle Z Z' Z
  rw [h.self, h.symm Z' Z] at h1
  linarith
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.pseudoMetric (h : IsDecayingPlacement κ S pl D) : IsPseudoMetricOnBonds (placementDist pl D) :=
  ⟨fun b => h.self _, fun b b' => h.symm _ _, fun b b' b'' => h.triangle _ _ _⟩
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.bond_sum_le (h : IsDecayingPlacement κ S pl D) (hκ : 0 < κ) {μ : ℝ} (hμ : κ / 2 ≤ μ) (Z : 𝒞) :
    ∑ b, Real.exp (-(μ * D Z (pl b))) ≤ S := by
  refine le_trans (Finset.sum_le_sum fun b _ => ?_) (h.bonds Z)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right hμ (h.dist_nonneg Z (pl b))
  linarith
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.cell_sum_le (h : IsDecayingPlacement κ S pl D) {μ : ℝ} (hμ : κ / 2 ≤ μ) (Z : 𝒞) :
    ∑ Z', Real.exp (-(μ * D Z Z')) ≤ S := by
  refine le_trans (Finset.sum_le_sum fun b _ => ?_) (h.cells Z)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right hμ (h.dist_nonneg Z b)
  linarith
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.const_nonneg (h : IsDecayingPlacement κ S pl D) (Z : 𝒞) : 0 ≤ S :=
  (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans (h.cells Z)
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsDecayingPlacement.one_le_const (h : IsDecayingPlacement κ S pl D) (Z : 𝒞) : 1 ≤ S := by
  refine le_trans ?_ (h.cells Z)
  have := Finset.single_le_sum (f := fun Z' => Real.exp (-(κ / 2 * D Z Z')))
    (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ Z)
  simpa [h.self] using this
theorem weightedSq_nonneg (Z : 𝒞) (η : BondField ι) : 0 ≤ weightedSqNormAt κ pl D Z η :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by positivity)
theorem weightedSq_continuous (Z : 𝒞) : Continuous (weightedSqNormAt (ι := ι) κ pl D Z) := by
  unfold weightedSqNormAt
  exact continuous_finset_sum _ fun b _ => by fun_prop
theorem weightedSq_mono (Z : 𝒞) {ζ η : BondField ι} (h : ∀ b, ‖ζ b‖ ≤ ‖η b‖) :
    weightedSqNormAt κ pl D Z ζ ≤ weightedSqNormAt κ pl D Z η := by
  unfold weightedSqNormAt
  refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact pow_le_pow_left₀ (norm_nonneg _) (h b) 2
theorem expectation_sq_bond_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x) (hl : 0 < lam)
    {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (b : ι) :
    ballExpectation r Ψ (fun η => ‖η b‖ ^ 2) ≤ 32 * S / (x * lam) := by
  obtain ⟨⟨K, hK⟩, s⟩ := hg
  have hm : 0 < x * lam / 4 := by positivity
  have hW : ∀ b₀, ∑ b, Real.exp (-(2 * κ * placementDist pl D b b₀)) ≤ S := fun b₀ => by
    have := hP.bond_sum_le hκ (μ := 2 * κ) (by linarith) (pl b₀)
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl fun b _ => by rw [placementDist, hP.symm]
  have := hmom ι ρ (x * lam / 4) κ S (placementDist pl D) Ψ K r hρ hm hκ.le hr hP.pseudoMetric hK hW s 1 b
  simp only [Finset.range_one, Finset.prod_singleton, CharP.cast_eq_zero, mul_zero, zero_add, pow_one,
    mul_one] at this
  refine this.trans (le_of_eq ?_)
  field_simp
  ring
theorem expectation_weightedSq_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x) (hl : 0 < lam)
    {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (Z : 𝒞) :
    ballExpectation r Ψ (weightedSqNormAt κ pl D Z) ≤ S * (32 * S / (x * lam)) := by
  have hΨ := hg.continuous_potential
  unfold weightedSqNormAt
  rw [expectation_sum _ _ hρ hr hΨ (fun b _ => by fun_prop)]
  calc _ = ∑ b, Real.exp (-(2 ^ 6 * κ * D Z (pl b))) * ballExpectation r Ψ (fun η => ‖η b‖ ^ 2) :=
        Finset.sum_congr rfl fun b _ => expectation_const_mul _
    _ ≤ ∑ b, Real.exp (-(2 ^ 6 * κ * D Z (pl b))) * (32 * S / (x * lam)) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (expectation_sq_bond_le hρ hr hmom hκ hP hx hl hg b) (Real.exp_pos _).le
    _ = (∑ b, Real.exp (-(2 ^ 6 * κ * D Z (pl b)))) * (32 * S / (x * lam)) := by
        rw [Finset.sum_mul]
    _ ≤ S * (32 * S / (x * lam)) := by
        apply mul_le_mul_of_nonneg_right (hP.bond_sum_le hκ (by nlinarith) Z)
        have := hP.const_nonneg Z
        positivity
def gradConstant (S lam : ℝ) : ℝ := Real.sqrt (2 + 64 * S ^ 2 / lam)
theorem gradConstant_nonneg (S lam : ℝ) : 0 ≤ gradConstant S lam := Real.sqrt_nonneg _
theorem l2Norm_le_of_linear_growth (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam)
    {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (Z : 𝒞)
    {f : BondField ι → ℝ} (hf : Continuous f) (hf0 : ∀ η, 0 ≤ f η) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ η ∈ openPolyball ι ρ, f η ≤ a * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1)) :
    ballL2Norm r Ψ f ≤ a * gradConstant S lam * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hΨ := hg.continuous_potential
  have hsq := weightedSq_continuous (κ := κ) (pl := pl) (D := D) (ι := ι) Z
  apply l2Norm_le (g := fun η => a ^ 2 * (2 * x ^ 2 * weightedSqNormAt κ pl D Z η + 2)) hρ hr hΨ hf
    (by fun_prop)
  · intro η hη
    have h1 := h η hη
    have h2 := weightedSq_nonneg (κ := κ) (pl := pl) (D := D) Z η
    have h3 := Real.sq_sqrt h2
    set u := Real.sqrt (weightedSqNormAt κ pl D Z η)
    have h4 : f η ^ 2 ≤ (a * (x * u + 1)) ^ 2 := pow_le_pow_left₀ (hf0 η) h1 2
    have h5 : (x * u + 1) ^ 2 ≤ 2 * x ^ 2 * weightedSqNormAt κ pl D Z η + 2 := by
      rw [← h3]
      nlinarith [sq_nonneg (x * u - 1)]
    calc f η ^ 2 ≤ (a * (x * u + 1)) ^ 2 := h4
      _ = a ^ 2 * (x * u + 1) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
  · rw [expectation_const_mul, show (fun η => 2 * x ^ 2 * weightedSqNormAt κ pl D Z η + 2) =
      fun η => (2 * x ^ 2) * weightedSqNormAt κ pl D Z η + 2 from rfl,
      expectation_add (f := fun η => (2 * x ^ 2) * weightedSqNormAt κ pl D Z η) (g := fun _ => 2) hρ hr hΨ
        (by fun_prop) continuous_const, expectation_const_mul, expectation_const hρ hr hΨ]
    have h1 := expectation_weightedSq_le hρ hr hmom hκ hP hx0 hl hg Z
    have h2 : (2 * x ^ 2) * ballExpectation r Ψ (weightedSqNormAt κ pl D Z) + 2 ≤
        x * (2 + 64 * S ^ 2 / lam) := by
      have h3 : (2 * x ^ 2) * ballExpectation r Ψ (weightedSqNormAt κ pl D Z) ≤
          (2 * x ^ 2) * (S * (32 * S / (x * lam))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : (2 * x ^ 2) * (S * (32 * S / (x * lam))) = x * (64 * S ^ 2 / lam) := by
        field_simp
        ring
      nlinarith
    have h5 : (a * gradConstant S lam * Real.sqrt x) ^ 2 = a ^ 2 * (x * (2 + 64 * S ^ 2 / lam)) := by
      rw [mul_pow, mul_pow, gradConstant, Real.sq_sqrt (by positivity), Real.sq_sqrt hx0.le]
      ring
    rw [h5]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  · have := gradConstant_nonneg S lam
    positivity
theorem abs_covariance_le_of_weights (hcov : CovarianceBoundHolds ρ r) (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x)
    (hl : 0 < lam) {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ)
    {f g : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (hg' : ContDiff ℝ 1 g) {u u' : ι → ℝ}
    (hu : ∀ b, ballL2Norm r Ψ (bondGradNorm f b) ≤ u b)
    (hu' : ∀ b, ballL2Norm r Ψ (bondGradNorm g b) ≤ u' b) :
    |ballCovariance r Ψ f g| ≤ (x * lam / 4)⁻¹ * ∑ b, ∑ b', u b * Real.exp (-(κ * placementDist pl D b b')) * u' b' := by
  obtain ⟨⟨K, hK⟩, _⟩ := hg
  have hm : 0 < x * lam / 4 := by positivity
  refine (hcov ι _ κ _ Ψ K hm hκ.le hP.pseudoMetric hK f g hf hg').trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
  have n1 : 0 ≤ ballL2Norm r Ψ (bondGradNorm f b) := Real.sqrt_nonneg _
  have n2 : 0 ≤ ballL2Norm r Ψ (bondGradNorm g b') := Real.sqrt_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hu b) (Real.exp_pos _).le) (hu' b') n2
    (mul_nonneg (n1.trans (hu b)) (Real.exp_pos _).le)
theorem double_sum_decay_le (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (Z₁ Z₂ : 𝒞) :
    ∑ b, ∑ b', Real.exp (-(2 * κ * D Z₁ (pl b))) * Real.exp (-(κ * placementDist pl D b b')) *
        Real.exp (-(2 * κ * D Z₂ (pl b'))) ≤ S ^ 2 * Real.exp (-(κ * D Z₁ Z₂)) := by
  have hterm : ∀ b b', Real.exp (-(2 * κ * D Z₁ (pl b))) * Real.exp (-(κ * placementDist pl D b b')) *
      Real.exp (-(2 * κ * D Z₂ (pl b'))) ≤ Real.exp (-(κ * D Z₁ Z₂)) *
        (Real.exp (-(κ * D Z₁ (pl b))) * Real.exp (-(κ * D Z₂ (pl b')))) := fun b b' => by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t1 := hP.triangle Z₁ (pl b) Z₂
    have t2 := hP.triangle (pl b) (pl b') Z₂
    have t3 := hP.symm (pl b') Z₂
    have : D Z₁ Z₂ ≤ D Z₁ (pl b) + placementDist pl D b b' + D Z₂ (pl b') := by
      unfold placementDist
      linarith
    nlinarith
  calc _ ≤ ∑ b, ∑ b', Real.exp (-(κ * D Z₁ Z₂)) *
        (Real.exp (-(κ * D Z₁ (pl b))) * Real.exp (-(κ * D Z₂ (pl b')))) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hterm b b'
    _ = Real.exp (-(κ * D Z₁ Z₂)) * ((∑ b, Real.exp (-(κ * D Z₁ (pl b)))) *
        ∑ b', Real.exp (-(κ * D Z₂ (pl b')))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(κ * D Z₁ Z₂)) * (S * S) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul (hP.bond_sum_le hκ (by linarith) _) (hP.bond_sum_le hκ (by linarith) _)
          (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (hP.const_nonneg Z₁)
    _ = _ := by ring
theorem abs_covariance_le_localized (hcov : CovarianceBoundHolds ρ r) (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x)
    (hl : 0 < lam) {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ)
    {f g : BondField ι → ℝ} (hf : ContDiff ℝ 1 f) (hg' : ContDiff ℝ 1 g) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (Z₁ Z₂ : 𝒞)
    (hu : ∀ b, ballL2Norm r Ψ (bondGradNorm f b) ≤
      h₁ * Real.sqrt x * Real.exp (-(2 * κ * D Z₁ (pl b))))
    (hu' : ∀ b, ballL2Norm r Ψ (bondGradNorm g b) ≤
      h₂ * Real.sqrt x * Real.exp (-(2 * κ * D Z₂ (pl b)))) :
    |ballCovariance r Ψ f g| ≤ 4 / lam * (h₁ * h₂) * S ^ 2 * Real.exp (-(κ * D Z₁ Z₂)) := by
  refine (abs_covariance_le_of_weights hcov hκ hP hx hl hg hf hg' hu hu').trans ?_
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have e1 : ∑ b, ∑ b', h₁ * Real.sqrt x * Real.exp (-(2 * κ * D Z₁ (pl b))) *
      Real.exp (-(κ * placementDist pl D b b')) * (h₂ * Real.sqrt x * Real.exp (-(2 * κ * D Z₂ (pl b')))) =
      (h₁ * h₂ * x) * ∑ b, ∑ b', Real.exp (-(2 * κ * D Z₁ (pl b))) *
        Real.exp (-(κ * placementDist pl D b b')) * Real.exp (-(2 * κ * D Z₂ (pl b'))) := by
    have e0 : h₁ * h₂ * x = h₁ * h₂ * (Real.sqrt x * Real.sqrt x) := by rw [hs]
    rw [e0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [e1]
  have h3 := double_sum_decay_le hκ hP Z₁ Z₂
  calc _ ≤ (x * lam / 4)⁻¹ * ((h₁ * h₂ * x) * (S ^ 2 * Real.exp (-(κ * D Z₁ Z₂)))) := by
        gcongr
    _ = _ := by
        field_simp
end Sizes
def nearConstant (S lam : ℝ) : ℝ := gradConstant S lam + S * Real.sqrt (32 * S / lam)
def squareConstant (S lam : ℝ) : ℝ := Real.sqrt (32 * S * lam)
def valueConstant (S lam : ℝ) : ℝ := 32 * S ^ 2 / lam + 1 + 16 * S / lam
section Step
variable {Λ ι 𝒞 : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] [Fintype 𝒞]
  [DecidableEq 𝒞] {ρ κ S lam x A rr : ℝ} {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {e : Λ → ι}
theorem nearConstant_nonneg (hS : 0 ≤ S) : 0 ≤ nearConstant S lam :=
  add_nonneg (gradConstant_nonneg _ _) (mul_nonneg hS (Real.sqrt_nonneg _))
theorem exp_neg_le_of_rate {a b u : ℝ} (hu : 0 ≤ u) (h : a ≤ b) : Real.exp (-(b * u)) ≤ Real.exp (-(a * u)) := by
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right h hu
  linarith
theorem weightedSq_freeze_le (he : Function.Injective e) (Z : 𝒞) (η : BondField ι) :
    weightedSqNormAt κ pl D Z (freezeMap e η) ≤ weightedSqNormAt κ pl D Z η :=
  weightedSq_mono Z (norm_freezeMap_le he η)
theorem gradNorm_freeze_le (hρ : 0 < ρ) (he : Function.Injective e) {g : BondField ι → ℝ}
    (hg : Differentiable ℝ g) {a w : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hw : 0 ≤ w) {Z : 𝒞} {b : ι}
    (h : ∀ ζ ∈ openPolyball ι ρ, bondGradNorm g b ζ ≤
      a * (x * Real.sqrt (weightedSqNormAt κ pl D Z ζ) + 1) * w) {η : BondField ι}
    (hη : η ∈ openPolyball ι ρ) :
    bondGradNorm (fun ζ => g (freezeMap e ζ)) b η ≤
      a * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) * w := by
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hb
    refine (gradNorm_freeze_mem_le he hg l η).trans ((h _ (freezeMap_mem_polyball hρ he hη)).trans ?_)
    have := Real.sqrt_le_sqrt (weightedSq_freeze_le (κ := κ) (pl := pl) (D := D) he Z η)
    gcongr
  · rw [gradNorm_freeze_off hg hb]
    have := Real.sqrt_nonneg (weightedSqNormAt κ pl D Z η)
    positivity
variable {θ : 𝒞 → BondField ι → ℝ} {Ψ H : BondField ι → ℝ} {Y : 𝒞}
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsLocalDecomposition.obs_diff (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y) :
    Differentiable ℝ H := hs.smooth_obs.differentiable (by simp)
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.IsLocalDecomposition.term_diff (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y) (Z : 𝒞) :
    Differentiable ℝ (θ Z) := (hs.smooth Z).differentiable (by simp)
theorem contDiff_comp_freeze {g : BondField ι → ℝ} {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun ζ => g (freezeMap e ζ)) := hg.comp (freezeMap e).contDiff
def freezeDefect (g : BondField ι → ℝ) (e : Λ → ι) (η : BondField ι) : ℝ := g η - g (freezeMap e η)
theorem freezeDefect_contDiff {g : BondField ι → ℝ} (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (freezeDefect g e) :=
  hg.sub (contDiff_comp_freeze hg)
section Measure
variable {M : BondField ι → ℝ}
theorem l2Norm_gradNorm_obs_segment_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) M) {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (b : ι) :
    ballL2Norm r M (bondGradNorm (segmentInterpolant (fun ζ => H (freezeMap e ζ)) H v) b) ≤
      (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 * κ * D Y (pl b))) := by
  have hx0 : 0 ≤ x := by linarith
  have hw : 0 ≤ Real.exp (-(2 ^ 5 * κ * D Y (pl b))) := (Real.exp_pos _).le
  have hsm : ContDiff ℝ 1 (segmentInterpolant (fun ζ => H (freezeMap e ζ)) H v) :=
    (contDiff_const.mul hs.smooth_obs).add (contDiff_const.mul (contDiff_comp_freeze hs.smooth_obs))
  have := l2Norm_le_of_linear_growth hρ hr hmom hκ hP hx hl hM Y (continuous_gradNorm hsm b)
    (gradNorm_nonneg _ _) (a := A * Real.exp (-(2 ^ 5 * κ * D Y (pl b)))) (by positivity)
    (fun η hη => by
      have e1 := hs.slope_obs η hη b
      have e2 := gradNorm_freeze_le hρ he hs.obs_diff hA hx0 hw (fun ζ hζ => hs.slope_obs ζ hζ b) hη
      have := gradNorm_segment_le (hs.obs_diff.comp (freezeMap e).differentiable) hs.obs_diff h0 h1 b η e2 e1
      refine this.trans (le_of_eq ?_)
      ring)
  refine this.trans ?_
  have h2 := exp_neg_le_of_rate (hP.dist_nonneg Y (pl b)) (a := 2 * κ) (b := 2 ^ 5 * κ) (by nlinarith)
  have h3 := gradConstant_nonneg S lam
  calc _ = (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 ^ 5 * κ * D Y (pl b))) := by ring
    _ ≤ _ := by gcongr
theorem l2Norm_gradNorm_defect_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) M) (Z : 𝒞) (b : ι) :
    ballL2Norm r M (bondGradNorm (freezeDefect (θ Z) e) b) ≤
      (2 * A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 * κ * D Z (pl b))) := by
  have hx0 : 0 ≤ x := by linarith
  have hw : 0 ≤ Real.exp (-(2 ^ 5 * κ * D Z (pl b))) := (Real.exp_pos _).le
  have hsm := freezeDefect_contDiff (e := e) ((hs.smooth Z).of_le (by norm_num) : ContDiff ℝ 1 (θ Z))
  have := l2Norm_le_of_linear_growth hρ hr hmom hκ hP hx hl hM Z (continuous_gradNorm hsm b)
    (gradNorm_nonneg _ _) (a := 2 * A * Real.exp (-(2 ^ 5 * κ * D Z (pl b)))) (by positivity)
    (fun η hη => by
      have e1 := hs.slope Z η hη b
      have e2 := gradNorm_freeze_le hρ he (hs.term_diff Z) hA hx0 hw (fun ζ hζ => hs.slope Z ζ hζ b) hη
      have := gradNorm_sub_le (hs.term_diff Z) ((hs.term_diff Z).comp (freezeMap e).differentiable) b η
      refine le_trans this ?_
      refine (add_le_add e1 e2).trans (le_of_eq ?_)
      ring)
  refine this.trans ?_
  have h2 := exp_neg_le_of_rate (hP.dist_nonneg Z (pl b)) (a := 2 * κ) (b := 2 ^ 5 * κ) (by nlinarith)
  have h3 := gradConstant_nonneg S lam
  calc _ = (2 * A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 ^ 5 * κ * D Z (pl b))) := by ring
    _ ≤ _ := by gcongr
theorem gradNorm_defect_mem_le (hρ : 0 < ρ) (hκ : 0 < κ) (hx : 0 ≤ x) (hA : 0 ≤ A)
    (he : Function.Injective e) (hP : IsDecayingPlacement κ S pl D)
    (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y) (Z : 𝒞) (l : Λ)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) :
    bondGradNorm (freezeDefect (θ Z) e) (e l) η ≤ A * x * Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) *
      ∑ c ∈ offBonds e, Real.exp (-(2 ^ 4 * κ * D Z (pl c))) * ‖η c‖ := by
  set B := A * x * Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) *
      ∑ c ∈ offBonds e, Real.exp (-(2 ^ 4 * κ * D Z (pl c))) * ‖η c‖ with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hθ2 := hs.smooth Z
  have hθd := hs.term_diff Z
  apply gradNorm_le_of_bound hB0
  intro w
  have hfd : fderiv ℝ (freezeDefect (θ Z) e) η (bondVariation (e l) w) =
      fderiv ℝ (θ Z) η (bondVariation (e l) w) - fderiv ℝ (θ Z) (freezeMap e η) (bondVariation (e l) w) := by
    have h1 : HasFDerivAt (freezeDefect (θ Z) e)
        (fderiv ℝ (θ Z) η - (fderiv ℝ (θ Z) (freezeMap e η)).comp (freezeMap e)) η :=
      (hθd η).hasFDerivAt.sub ((hθd _).hasFDerivAt.comp η (freezeMap e).hasFDerivAt)
    rw [h1.fderiv]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, freezeMap_bondVariation_mem he]
  rw [hfd]
  have h1 : freezePath e η 1 = η := by simp [freezePath]
  have h0 : freezePath e η 0 = freezeMap e η := by simp [freezePath]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => fderiv ℝ (θ Z) (freezePath e η s) (bondVariation (e l) w))
    (f' := fun s => secondDerivAlong (θ Z) (freezePath e η s) (bondVariation (e l) w) (η - freezeMap e η))
    (s := Set.Icc (0 : ℝ) 1) (C := B * ‖w‖) (x := 0) (y := 1)
    (fun s _ => (((differentiable_fderiv_apply_const hθ2 _ _).hasFDerivAt.comp_hasDerivAt s
      (freezePath_hasDerivAt η s))).hasDerivWithinAt)
    (fun s hs' => ?_) (convex_Icc 0 1) (by simp) (by simp)
  · simpa [h1, h0, abs_sub_comm] using key
  · have hmem := freezePath_mem he hη hs'.1 hs'.2
    rw [sub_freezeMap_eq_sum he]
    have hsum : secondDerivAlong (θ Z) (freezePath e η s) (bondVariation (e l) w) (∑ c ∈ offBonds e, bondVariation c (η c)) =
        ∑ c ∈ offBonds e, secondDerivAlong (θ Z) (freezePath e η s) (bondVariation (e l) w) (bondVariation c (η c)) := by
      unfold secondDerivAlong
      exact map_sum _ _ _
    rw [hsum, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ c ∈ offBonds e, |secondDerivAlong (θ Z) (freezePath e η s) (bondVariation (e l) w) (bondVariation c (η c))| ≤
        A * x * Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) *
          (Real.exp (-(2 ^ 4 * κ * D Z (pl c))) * ‖η c‖) * ‖w‖ := fun c _ => by
      refine (hs.second Z _ hmem _ _ w (η c)).trans ?_
      have hexp : Real.exp (-(2 ^ 5 * κ * max (D Z (pl (e l))) (D Z (pl c)))) ≤
          Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) * Real.exp (-(2 ^ 4 * κ * D Z (pl c))) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have m1 := le_max_left (D Z (pl (e l))) (D Z (pl c))
        have m2 := le_max_right (D Z (pl (e l))) (D Z (pl c))
        nlinarith
      calc _ ≤ A * x * (Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) *
            Real.exp (-(2 ^ 4 * κ * D Z (pl c)))) * ‖w‖ * ‖η c‖ := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [hBdef, Finset.mul_sum, Finset.sum_mul]
theorem l2Norm_gradNorm_defect_le_of_far (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A) (hrr : 0 ≤ rr)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) M) (Z : 𝒞)
    (hZ : ∀ c, c ∉ Set.range e → rr / 2 ≤ D Z (pl c)) (b : ι) :
    ballL2Norm r M (bondGradNorm (freezeDefect (θ Z) e) b) ≤
      (A * nearConstant S lam * Real.exp (-(4 * κ * rr))) * Real.sqrt x * Real.exp (-(2 * κ * D Z (pl b))) := by
  have hx0 : 0 < x := by linarith
  have hS : 0 ≤ S := hP.const_nonneg Z
  have hsm := freezeDefect_contDiff (e := e) ((hs.smooth Z).of_le (by norm_num) : ContDiff ℝ 1 (θ Z))
  have hMc := hM.continuous_potential
  have hq := hP.dist_nonneg Z (pl b)
  have hc0 := gradConstant_nonneg S lam
  have hsq : 0 ≤ Real.sqrt (32 * S / lam) := Real.sqrt_nonneg _
  have hc1 : 0 ≤ nearConstant S lam := nearConstant_nonneg hS
  by_cases hb : b ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hb
    set c : ι → ℝ := fun c => Real.exp (-(2 ^ 4 * κ * D Z (pl c))) with hcdef
    have hc : ∀ c', 0 ≤ c c' := fun c' => (Real.exp_pos _).le
    set T : ℝ := Real.exp (-(4 * κ * rr)) * S with hT
    have hsumc : ∑ c' ∈ offBonds e, c c' ≤ T := by
      calc _ ≤ ∑ c' ∈ offBonds e, Real.exp (-(4 * κ * rr)) * Real.exp (-(8 * κ * D Z (pl c'))) := by
            refine Finset.sum_le_sum fun c' hc' => ?_
            rw [hcdef, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h1 := hZ c' (mem_offBonds.mp hc')
            nlinarith
        _ = Real.exp (-(4 * κ * rr)) * ∑ c' ∈ offBonds e, Real.exp (-(8 * κ * D Z (pl c'))) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (-(4 * κ * rr)) * ∑ c', Real.exp (-(8 * κ * D Z (pl c'))) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun _ _ _ => (Real.exp_pos _).le
        _ ≤ T := by
            apply mul_le_mul_of_nonneg_left (hP.bond_sum_le hκ (by linarith) Z) (Real.exp_pos _).le
    set p := Real.exp (-(2 ^ 4 * κ * D Z (pl (e l)))) with hp
    have hpoint : ∀ η ∈ openPolyball ι ρ, bondGradNorm (freezeDefect (θ Z) e) (e l) η ^ 2 ≤
        (A ^ 2 * x ^ 2 * p ^ 2 * T) * ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2 := fun η hη => by
      have h1 := gradNorm_defect_mem_le hρ hκ hx0.le hA he hP hs Z l hη
      have h2 : (∑ c' ∈ offBonds e, c c' * ‖η c'‖) ^ 2 ≤
          (∑ c' ∈ offBonds e, c c') * ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2 :=
        Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun c' _ => hc c')
          (fun c' _ => mul_nonneg (hc c') (by positivity)) (fun c' _ => by ring)
      have h3 : 0 ≤ ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2 :=
        Finset.sum_nonneg fun c' _ => mul_nonneg (hc c') (by positivity)
      calc _ ≤ (A * x * p * ∑ c' ∈ offBonds e, c c' * ‖η c'‖) ^ 2 :=
            pow_le_pow_left₀ (gradNorm_nonneg _ _ _) h1 2
        _ = A ^ 2 * x ^ 2 * p ^ 2 * (∑ c' ∈ offBonds e, c c' * ‖η c'‖) ^ 2 := by ring
        _ ≤ A ^ 2 * x ^ 2 * p ^ 2 * (T * ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact h2.trans (mul_le_mul_of_nonneg_right hsumc h3)
        _ = _ := by ring
    have hcont : Continuous fun η : BondField ι =>
        (A ^ 2 * x ^ 2 * p ^ 2 * T) * ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2 := by
      refine continuous_const.mul (continuous_finset_sum _ fun c' _ => by fun_prop)
    have hmean : ballExpectation r M (fun η => (A ^ 2 * x ^ 2 * p ^ 2 * T) *
        ∑ c' ∈ offBonds e, c c' * ‖η c'‖ ^ 2) ≤
        (A * p * T * Real.sqrt (32 * S / lam) * Real.sqrt x) ^ 2 := by
      rw [expectation_const_mul, expectation_sum _ _ hρ hr hMc (fun c' _ => by fun_prop)]
      have h1 : ∑ c' ∈ offBonds e, ballExpectation r M (fun η => c c' * ‖η c'‖ ^ 2) ≤
          T * (32 * S / (x * lam)) := by
        calc _ = ∑ c' ∈ offBonds e, c c' * ballExpectation r M (fun η => ‖η c'‖ ^ 2) :=
              Finset.sum_congr rfl fun c' _ => expectation_const_mul _
          _ ≤ ∑ c' ∈ offBonds e, c c' * (32 * S / (x * lam)) :=
              Finset.sum_le_sum fun c' _ => mul_le_mul_of_nonneg_left
                (expectation_sq_bond_le hρ hr hmom hκ hP hx0 hl hM c') (hc c')
          _ = (∑ c' ∈ offBonds e, c c') * (32 * S / (x * lam)) := by rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hsumc (by positivity)
      calc _ ≤ (A ^ 2 * x ^ 2 * p ^ 2 * T) * (T * (32 * S / (x * lam))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by
            rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
              Real.sq_sqrt hx0.le]
            field_simp
    have hn := l2Norm_le hρ hr hMc (continuous_gradNorm hsm (e l)) hcont hpoint hmean
      (by positivity)
    refine hn.trans ?_
    have e3 : p ≤ Real.exp (-(2 * κ * D Z (pl (e l)))) :=
      exp_neg_le_of_rate (hP.dist_nonneg _ _) (by nlinarith)
    have e4 : S * Real.sqrt (32 * S / lam) ≤ nearConstant S lam := by
      unfold nearConstant
      linarith
    calc A * p * T * Real.sqrt (32 * S / lam) * Real.sqrt x =
          A * (S * Real.sqrt (32 * S / lam)) * Real.exp (-(4 * κ * rr)) * Real.sqrt x * p := by
          rw [hT]; ring
      _ ≤ _ := by gcongr
  · have hw : 0 ≤ Real.exp (-(2 ^ 5 * κ * D Z (pl b))) := (Real.exp_pos _).le
    have := l2Norm_le_of_linear_growth hρ hr hmom hκ hP hx hl hM Z (continuous_gradNorm hsm b)
      (gradNorm_nonneg _ _) (a := A * Real.exp (-(2 ^ 5 * κ * D Z (pl b)))) (by positivity)
      (fun η hη => by
        have e1 := hs.slope Z η hη b
        have e2 := gradNorm_freeze_off (hs.term_diff Z) hb η
        have e3 := gradNorm_sub_le (hs.term_diff Z) ((hs.term_diff Z).comp (freezeMap e).differentiable) b η
        have e4 : bondGradNorm (freezeDefect (θ Z) e) b η ≤ bondGradNorm (θ Z) b η + 0 := by
          rw [← e2]
          exact e3
        refine e4.trans ?_
        rw [add_zero]
        refine e1.trans (le_of_eq ?_)
        ring)
    refine this.trans ?_
    have hZb := hZ b hb
    have e5 : Real.exp (-(2 ^ 5 * κ * D Z (pl b))) ≤
        Real.exp (-(4 * κ * rr)) * Real.exp (-(2 * κ * D Z (pl b))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have e6 : gradConstant S lam ≤ nearConstant S lam := by
      unfold nearConstant
      have := mul_nonneg hS hsq
      linarith
    calc _ = A * gradConstant S lam * Real.sqrt x * Real.exp (-(2 ^ 5 * κ * D Z (pl b))) := by ring
      _ ≤ A * nearConstant S lam * Real.sqrt x * (Real.exp (-(4 * κ * rr)) * Real.exp (-(2 * κ * D Z (pl b)))) := by
        gcongr
      _ = _ := by ring
theorem gradNorm_offBondsSq_le (c : ℝ) (hc : 0 ≤ c) (b : ι) (η : BondField ι) :
    bondGradNorm (offBondsSq e c) b η ≤ if b ∈ offBonds e then 2 * c * ‖η b‖ else 0 := by
  have hB : 0 ≤ if b ∈ offBonds e then 2 * c * ‖η b‖ else 0 := by
    split_ifs
    · positivity
    · exact le_rfl
  apply gradNorm_le_of_bound hB
  intro w
  rw [(offBondsSq_hasFDerivAt c η).fderiv]
  simp only [ContinuousLinearMap.smul_apply, pairingMap_apply, smul_eq_mul]
  have h1 : ∑ c' ∈ offBonds e, ⟪η c', bondVariation b w c'⟫ = if b ∈ offBonds e then ⟪η b, w⟫ else 0 := by
    by_cases hb : b ∈ offBonds e
    · rw [if_pos hb, Finset.sum_eq_single b]
      · simp [bondVariation]
      · intro c' _ hc'
        simp [bondVariation, hc']
      · exact fun h => absurd hb h
    · rw [if_neg hb]
      apply Finset.sum_eq_zero
      intro c' hc'
      have : c' ≠ b := fun h => hb (h ▸ hc')
      simp [bondVariation, this]
  rw [h1]
  by_cases hb : b ∈ offBonds e
  · simp only [if_pos hb]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * c)]
    have := abs_real_inner_le_norm (η b) w
    calc 2 * c * |⟪η b, w⟫| ≤ 2 * c * (‖η b‖ * ‖w‖) := by gcongr
      _ = _ := by ring
  · simp [if_neg hb]
theorem abs_covariance_offBondsSq_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hcov : CovarianceBoundHolds ρ r) (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) M) {f : BondField ι → ℝ}
    (hf : ContDiff ℝ 1 f) {h₁ : ℝ} (hh₁ : 0 ≤ h₁) (hrr : 0 ≤ rr)
    (hu : ∀ b, ballL2Norm r M (bondGradNorm f b) ≤ h₁ * Real.sqrt x * Real.exp (-(2 * κ * D Y (pl b))))
    (hoff : ∀ c, c ∉ Set.range e → rr ≤ D Y (pl c)) :
    |ballCovariance r M f (offBondsSq e (x * lam / 2))| ≤
      4 / lam * (h₁ * squareConstant S lam) * S ^ 2 * Real.exp (-(κ * rr / 2)) := by
  have hx0 : 0 < x := by linarith
  have hMc := hM.continuous_potential
  have hS : 0 ≤ S := hP.const_nonneg Y
  have hc : 0 ≤ x * lam / 2 := by positivity
  have hQ : ContDiff ℝ 1 (offBondsSq e (x * lam / 2)) := (offBondsSq_contDiff _).of_le (by norm_num)
  have hc2 : 0 ≤ squareConstant S lam := Real.sqrt_nonneg _
  have hu' : ∀ b, ballL2Norm r M (bondGradNorm (offBondsSq e (x * lam / 2)) b) ≤
      if b ∈ offBonds e then squareConstant S lam * Real.sqrt x else 0 := fun b => by
    by_cases hb : b ∈ offBonds e
    · rw [if_pos hb]
      apply l2Norm_le (g := fun η => (x * lam) ^ 2 * ‖η b‖ ^ 2) hρ hr hMc
        (continuous_gradNorm hQ b) (by fun_prop)
      · intro η _
        have h1 := gradNorm_offBondsSq_le (e := e) _ hc b η
        rw [if_pos hb] at h1
        have h2 := pow_le_pow_left₀ (gradNorm_nonneg _ _ _) h1 2
        refine h2.trans (le_of_eq ?_)
        ring
      · rw [expectation_const_mul]
        have h1 := expectation_sq_bond_le hρ hr hmom hκ hP hx0 hl hM b
        calc _ ≤ (x * lam) ^ 2 * (32 * S / (x * lam)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by
              have e1 : (squareConstant S lam * Real.sqrt x) ^ 2 = 32 * S * lam * x := by
                rw [mul_pow, squareConstant, Real.sq_sqrt (by positivity), Real.sq_sqrt hx0.le]
              rw [e1]
              field_simp
      · positivity
    · rw [if_neg hb]
      have hz : ∀ η, bondGradNorm (offBondsSq e (x * lam / 2)) b η = 0 := fun η => by
        have h1 := gradNorm_offBondsSq_le (e := e) _ hc b η
        rw [if_neg hb] at h1
        exact le_antisymm h1 (gradNorm_nonneg _ _ _)
      unfold ballL2Norm
      simp [hz, expectation_const_mul]
      have := expectation_const hρ hr hMc 0
      simp [this]
  refine (abs_covariance_le_of_weights hcov hκ hP hx0 hl hM hf hQ hu hu').trans ?_
  set E := Real.exp (-(κ * rr / 2)) with hE
  have hterm : ∀ b b', (h₁ * Real.sqrt x * Real.exp (-(2 * κ * D Y (pl b)))) *
      Real.exp (-(κ * placementDist pl D b b')) * (if b' ∈ offBonds e then squareConstant S lam * Real.sqrt x else 0) ≤
      (h₁ * squareConstant S lam * x * E) * (Real.exp (-(κ * D Y (pl b))) * Real.exp (-(κ / 2 * D Y (pl b')))) := fun b b' => by
    by_cases hb' : b' ∈ offBonds e
    · rw [if_pos hb']
      have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      have h2 : Real.exp (-(2 * κ * D Y (pl b))) * Real.exp (-(κ * placementDist pl D b b')) ≤
          E * (Real.exp (-(κ * D Y (pl b))) * Real.exp (-(κ / 2 * D Y (pl b')))) := by
        rw [hE, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have t1 := hP.triangle Y (pl b) (pl b')
        have t2 := hoff b' (mem_offBonds.mp hb')
        unfold placementDist
        nlinarith
      calc _ = (h₁ * squareConstant S lam * (Real.sqrt x * Real.sqrt x)) * (Real.exp (-(2 * κ * D Y (pl b))) *
            Real.exp (-(κ * placementDist pl D b b'))) := by ring
        _ ≤ _ := by
            rw [hs]
            rw [mul_assoc (h₁ * squareConstant S lam * x) E]
            exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h2) (by positivity)
    · rw [if_neg hb', mul_zero]
      have := (Real.exp_pos (-(κ * D Y (pl b)))).le
      have := (Real.exp_pos (-(κ / 2 * D Y (pl b')))).le
      have : 0 ≤ E := (Real.exp_pos _).le
      positivity
  have hsum : ∑ b, ∑ b', (h₁ * Real.sqrt x * Real.exp (-(2 * κ * D Y (pl b)))) *
      Real.exp (-(κ * placementDist pl D b b')) * (if b' ∈ offBonds e then squareConstant S lam * Real.sqrt x else 0) ≤
      (h₁ * squareConstant S lam * x * E) * (S * S) := by
    calc _ ≤ ∑ b, ∑ b', (h₁ * squareConstant S lam * x * E) * (Real.exp (-(κ * D Y (pl b))) *
          Real.exp (-(κ / 2 * D Y (pl b')))) :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hterm b b'
      _ = (h₁ * squareConstant S lam * x * E) * ((∑ b, Real.exp (-(κ * D Y (pl b)))) *
          ∑ b', Real.exp (-(κ / 2 * D Y (pl b')))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by have : 0 ≤ E := (Real.exp_pos _).le; positivity)
          exact mul_le_mul (hP.bond_sum_le hκ (by linarith) _) (hP.bond_sum_le hκ le_rfl _)
            (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hS
  calc _ ≤ (x * lam / 4)⁻¹ * ((h₁ * squareConstant S lam * x * E) * (S * S)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
        field_simp
theorem abs_expectation_obs_sub_freeze_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A) (hrr : 0 ≤ rr)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) M)
    (hoff : ∀ c, c ∉ Set.range e → rr ≤ D Y (pl c)) :
    |ballExpectation r M (fun η => H η - H (freezeMap e η))| ≤
      A * valueConstant S lam * S * Real.exp (-(16 * κ * rr)) := by
  have hx0 : 0 < x := by linarith
  have hMc := hM.continuous_potential
  have hS1 : 1 ≤ S := hP.one_le_const Y
  set w : ι → ℝ := fun c => Real.exp (-(2 ^ 5 * κ * D Y (pl c))) with hw
  have hw0 : ∀ c, 0 ≤ w c := fun c => (Real.exp_pos _).le
  have hsq := weightedSq_continuous (κ := κ) (pl := pl) (D := D) (ι := ι) Y
  set G : BondField ι → ℝ := fun η => A * ∑ c ∈ offBonds e, w c *
    (x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) + (1 + ‖η c‖ ^ 2) / 2) with hG
  have hGc : Continuous G := continuous_const.mul (continuous_finset_sum _ fun c _ => by fun_prop)
  have hHc : Continuous fun η => H η - H (freezeMap e η) :=
    hs.smooth_obs.continuous.sub (contDiff_comp_freeze hs.smooth_obs).continuous
  have hpoint : ∀ η ∈ openPolyball ι ρ, |H η - H (freezeMap e η)| ≤ G η := fun η hη => by
    refine abs_sub_freeze_le (ρ := ρ) hs.obs_diff he fun s h0 h1 => ?_
    rw [sub_freezeMap_eq_sum he, map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    change _ ≤ A * ∑ c ∈ offBonds e, w c *
      (x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) + (1 + ‖η c‖ ^ 2) / 2)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hm := freezePath_mem he hη h0 h1
    have h2 := (abs_fderiv_bondVariation_le_gradNorm H c _ (η c)).trans (mul_le_mul_of_nonneg_right
      (hs.slope_obs _ hm c) (norm_nonneg _))
    refine h2.trans ?_
    have h3 := Real.sqrt_le_sqrt (weightedSq_mono (κ := κ) (pl := pl) (D := D) Y
      (norm_freezePath_le he η h0 h1))
    have h4 := weightedSq_nonneg (κ := κ) (pl := pl) (D := D) Y η
    have h5 := Real.sq_sqrt h4
    set u := Real.sqrt (weightedSqNormAt κ pl D Y η)
    set n := ‖η c‖
    have h6 : (x * u + 1) * n ≤ x / 2 * (weightedSqNormAt κ pl D Y η + n ^ 2) + (1 + n ^ 2) / 2 := by
      rw [← h5]
      nlinarith [sq_nonneg (u - n), sq_nonneg (n - 1)]
    calc _ ≤ A * (x * u + 1) * w c * n := by
          gcongr
      _ = A * w c * ((x * u + 1) * n) := by ring
      _ ≤ A * w c * (x / 2 * (weightedSqNormAt κ pl D Y η + n ^ 2) + (1 + n ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h6 (mul_nonneg hA (hw0 c))
      _ = _ := by ring
  refine (abs_expectation_le hρ hr hMc hHc hGc hpoint).trans ?_
  have hmo := fun c => expectation_sq_bond_le hρ hr hmom hκ hP hx0 hl hM (b := c)
  have hsm := expectation_weightedSq_le hρ hr hmom hκ hP hx0 hl hM Y
  set Mo := 32 * S / (x * lam) with hMo
  have hbr : ∀ c, ballExpectation r M (fun η => x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) +
      (1 + ‖η c‖ ^ 2) / 2) ≤ valueConstant S lam := fun c => by
    have e1 : (fun η : BondField ι => x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) +
        (1 + ‖η c‖ ^ 2) / 2) = fun η => (x / 2) * weightedSqNormAt κ pl D Y η +
          ((x / 2 + 1 / 2) * ‖η c‖ ^ 2 + 1 / 2) := by
      funext η; ring
    rw [e1, expectation_add (f := fun η => (x / 2) * weightedSqNormAt κ pl D Y η) hρ hr hMc (by fun_prop)
      (by fun_prop), expectation_add (f := fun η => (x / 2 + 1 / 2) * ‖η c‖ ^ 2) (g := fun _ => 1 / 2) hρ hr
      hMc (by fun_prop) continuous_const, expectation_const_mul, expectation_const_mul, expectation_const hρ hr hMc]
    have h1 := mul_le_mul_of_nonneg_left hsm (by positivity : 0 ≤ x / 2)
    have h2 := mul_le_mul_of_nonneg_left (hmo c) (by positivity : 0 ≤ x / 2 + 1 / 2)
    have e2 : x / 2 * (S * Mo) = 16 * S ^ 2 / lam := by
      rw [hMo]; field_simp; ring
    have e3 : (x / 2 + 1 / 2) * Mo ≤ 32 * S / lam := by
      have : Mo ≤ 32 * S / lam := by
        rw [hMo]
        apply div_le_div_of_nonneg_left (by positivity) hl
        nlinarith
      have e4 : x / 2 * Mo = 16 * S / lam := by
        rw [hMo]; field_simp; ring
      have e5 : 32 * S / lam = 2 * (16 * S / lam) := by ring
      nlinarith
    have e6 : 32 * S / lam ≤ 16 * S ^ 2 / lam + 16 * S / lam := by
      have : 32 * S ≤ 16 * S ^ 2 + 16 * S := by nlinarith
      rw [← add_div]
      exact div_le_div_of_nonneg_right this hl.le
    have e8 : 32 * S ^ 2 / lam = 2 * (16 * S ^ 2 / lam) := by ring
    unfold valueConstant
    rw [e8]
    rw [e2] at h1
    linarith
  have hsumw : ∑ c ∈ offBonds e, w c ≤ Real.exp (-(16 * κ * rr)) * S := by
    calc _ ≤ ∑ c ∈ offBonds e, Real.exp (-(16 * κ * rr)) * Real.exp (-(16 * κ * D Y (pl c))) := by
          refine Finset.sum_le_sum fun c hc => ?_
          rw [hw, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h1 := hoff c (mem_offBonds.mp hc)
          nlinarith
      _ = Real.exp (-(16 * κ * rr)) * ∑ c ∈ offBonds e, Real.exp (-(16 * κ * D Y (pl c))) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp (-(16 * κ * rr)) * ∑ c, Real.exp (-(16 * κ * D Y (pl c))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => (Real.exp_pos _).le
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (hP.bond_sum_le hκ (by linarith) Y) (Real.exp_pos _).le
  have hc30 : 0 ≤ valueConstant S lam := by unfold valueConstant; positivity
  rw [hG, expectation_const_mul, expectation_sum _ _ hρ hr hMc (fun c _ => by fun_prop)]
  have : ∑ c ∈ offBonds e, ballExpectation r M (fun η => w c * (x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) +
      (1 + ‖η c‖ ^ 2) / 2)) ≤ (Real.exp (-(16 * κ * rr)) * S) * valueConstant S lam := by
    calc _ = ∑ c ∈ offBonds e, w c * ballExpectation r M (fun η => x / 2 * (weightedSqNormAt κ pl D Y η + ‖η c‖ ^ 2) +
          (1 + ‖η c‖ ^ 2) / 2) := Finset.sum_congr rfl fun c _ => expectation_const_mul _
      _ ≤ ∑ c ∈ offBonds e, w c * valueConstant S lam :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hbr c) (hw0 c)
      _ = (∑ c ∈ offBonds e, w c) * valueConstant S lam := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsumw hc30
  calc _ ≤ A * ((Real.exp (-(16 * κ * rr)) * S) * valueConstant S lam) := mul_le_mul_of_nonneg_left this hA
    _ = _ := by ring
end Measure
end Step
def sideConstant (S lam : ℝ) : ℝ :=
  4 / lam * (gradConstant S lam * (2 * nearConstant S lam)) * S ^ 3 + 4 / lam * (gradConstant S lam * squareConstant S lam) * S ^ 2 +
    valueConstant S lam * S
section Side
variable {Λ ι 𝒞 : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι] [Fintype 𝒞]
  [DecidableEq 𝒞] {ρ κ S lam x A rr : ℝ} {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {e : Λ → ι}
  {θ : 𝒞 → BondField ι → ℝ} {Ψ H : BondField ι → ℝ} {Y : 𝒞}
theorem exists_bound_polyball (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : Continuous f) :
    ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.exists_abs_le_on_ballProduct <;> assumption
theorem exists_common_bound_polyball (hρ : 0 < ρ) {f g h k : BondField ι → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    ∃ M, ∀ η ∈ openPolyball ι ρ, |f η| ≤ M ∧ |g η| ≤ M ∧ |h η| ≤ M ∧ |k η| ≤ M := by
  obtain ⟨a, ha⟩ := exists_bound_polyball hρ hf
  obtain ⟨b, hb⟩ := exists_bound_polyball hρ hg
  obtain ⟨c, hc⟩ := exists_bound_polyball hρ hh
  obtain ⟨d, hd⟩ := exists_bound_polyball hρ hk
  refine ⟨max (max a b) (max c d), fun η hη => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (ha η hη).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hb η hη).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hc η hη).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hd η hη).trans ((le_max_right _ _).trans (le_max_right _ _))
theorem abs_expectation_sub_frozen_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hseg : MeanDifferenceBoundAlongSegment)
    (hmom : GaussianMomentBound) (hcov : CovarianceBoundHolds ρ r)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 1 ≤ A) (hrr : 0 ≤ rr)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hΨ : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ)
    (hoff : ∀ c, c ∉ Set.range e → rr ≤ D Y (pl c)) :
    |ballExpectation r Ψ H - ballExpectation r (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2)) (fun η => H (freezeMap e η))| ≤
      sideConstant S lam * (A ^ 2 * Real.exp (-(κ * rr / 4))) := by
  have hx0 : 0 < x := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hm : 0 < x * lam / 4 := by positivity
  have hS1 : 1 ≤ S := hP.one_le_const Y
  have hS : 0 ≤ S := by linarith
  have hc0 := gradConstant_nonneg S lam
  have hc1 : 0 ≤ nearConstant S lam := nearConstant_nonneg hS
  have hc01 : gradConstant S lam ≤ nearConstant S lam := by
    unfold nearConstant
    have := mul_nonneg hS (Real.sqrt_nonneg (32 * S / lam))
    linarith
  have hc2 : 0 ≤ squareConstant S lam := Real.sqrt_nonneg _
  have hc3 : 0 ≤ valueConstant S lam := by unfold valueConstant; positivity
  have hF : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2)) :=
    hΨ.freeze hρ hκ.le hm (by nlinarith) he hP.pseudoMetric
  set E := Real.exp (-(κ * rr / 4)) with hE
  have hFc := hF.continuous_potential
  have hΨc := hΨ.continuous_potential
  have hH₀ := contDiff_comp_freeze (e := e) hs.smooth_obs
  obtain ⟨Mb, hMb⟩ := exists_common_bound_polyball hρ hFc hΨc hH₀.continuous hs.smooth_obs.continuous
  have hA2 : A ≤ A ^ 2 := by nlinarith
  refine hseg ι ρ r (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2)) Ψ (fun ζ => H (freezeMap e ζ)) H Mb _ hρ hr
    hFc.continuousOn hΨc.continuousOn hH₀.continuous.continuousOn hs.smooth_obs.continuous.continuousOn
    hMb fun v h0 h1 => ?_
  have hM := hF.interpolate hm hΨ h0 h1
  have hMc := hM.continuous_potential
  set M := segmentInterpolant (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2)) Ψ v with hMdef
  set Hv := segmentInterpolant (fun ζ => H (freezeMap e ζ)) H v with hHv
  have hHs : ContDiff ℝ 1 Hv := (contDiff_const.mul hs.smooth_obs).add (contDiff_const.mul hH₀)
  have hsizeH := fun b => l2Norm_gradNorm_obs_segment_le hρ hr hmom hκ hP hx hl hA0 he hs hM h0 h1 b
  have hδ : ∀ Z, ContDiff ℝ 1 (freezeDefect (θ Z) e) := fun Z => freezeDefect_contDiff ((hs.smooth Z).of_le (by norm_num))
  have hQ : ContDiff ℝ 1 (offBondsSq e (x * lam / 2)) := (offBondsSq_contDiff _).of_le (by norm_num)
  have hcg : ballCovariance r M Hv (fun η => Ψ η - _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2) η) =
      (∑ Z, ballCovariance r M Hv (freezeDefect (θ Z) e)) - ballCovariance r M Hv (offBondsSq e (x * lam / 2)) := by
    rw [covariance_congr (g' := fun η => (∑ Z, freezeDefect (θ Z) e η) - offBondsSq e (x * lam / 2) η) hr
      (fun _ _ => rfl) (fun _ _ => rfl) (fun η hη => ?_),
      covariance_sub (g := fun η => ∑ Z, freezeDefect (θ Z) e η) hρ hr hMc hHs.continuous
        (continuous_finset_sum _ fun Z _ => (hδ Z).continuous) hQ.continuous,
      covariance_sum _ _ hρ hr hMc hHs.continuous fun Z _ => (hδ Z).continuous]
    simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential, freezeDefect, Finset.sum_sub_distrib]
    rw [hs.sum η hη, hs.sum _ (freezeMap_mem_polyball hρ he hη)]
    ring
  rw [hcg]
  have hterm : ∀ Z, |ballCovariance r M Hv (freezeDefect (θ Z) e)| ≤
      4 / lam * ((A * gradConstant S lam) * (2 * A * nearConstant S lam)) * S ^ 2 * E *
        Real.exp (-(κ / 2 * D Y Z)) := fun Z => by
    have hDn := hP.dist_nonneg Y Z
    by_cases hZ : D Y Z < rr / 2
    · have hfar : ∀ c, c ∉ Set.range e → rr / 2 ≤ D Z (pl c) := fun c hc => by
        have t1 := hP.triangle Y Z (pl c)
        have t2 := hoff c hc
        linarith
      have h1 := abs_covariance_le_localized hcov hκ hP hx0 hl hM hHs (hδ Z) (h₁ := A * gradConstant S lam)
        (h₂ := A * nearConstant S lam * Real.exp (-(4 * κ * rr))) (by positivity) (by positivity) Y Z hsizeH
        (l2Norm_gradNorm_defect_le_of_far hρ hr hmom hκ hP hx hl hA0 hrr he hs hM Z hfar)
      refine h1.trans ?_
      have e1 : Real.exp (-(4 * κ * rr)) * Real.exp (-(κ * D Y Z)) ≤
          E * Real.exp (-(κ / 2 * D Y Z)) := by
        rw [hE, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc _ = 4 / lam * ((A * gradConstant S lam) * (A * nearConstant S lam)) * S ^ 2 *
            (Real.exp (-(4 * κ * rr)) * Real.exp (-(κ * D Y Z))) := by ring
        _ ≤ 4 / lam * ((A * gradConstant S lam) * (A * nearConstant S lam)) * S ^ 2 *
            (E * Real.exp (-(κ / 2 * D Y Z))) := by gcongr
        _ ≤ 4 / lam * ((A * gradConstant S lam) * (2 * A * nearConstant S lam)) * S ^ 2 *
            (E * Real.exp (-(κ / 2 * D Y Z))) := by
            have : 0 ≤ E * Real.exp (-(κ / 2 * D Y Z)) := by positivity
            gcongr
            nlinarith
        _ = _ := by ring
    · have hZ' : rr / 2 ≤ D Y Z := not_lt.mp hZ
      have h1 := abs_covariance_le_localized hcov hκ hP hx0 hl hM hHs (hδ Z) (h₁ := A * gradConstant S lam)
        (h₂ := 2 * A * gradConstant S lam) (by positivity) (by positivity) Y Z hsizeH
        (l2Norm_gradNorm_defect_le hρ hr hmom hκ hP hx hl hA0 he hs hM Z)
      refine h1.trans ?_
      have e1 : Real.exp (-(κ * D Y Z)) ≤ E * Real.exp (-(κ / 2 * D Y Z)) := by
        rw [hE, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      calc _ ≤ 4 / lam * ((A * gradConstant S lam) * (2 * A * gradConstant S lam)) * S ^ 2 *
            (E * Real.exp (-(κ / 2 * D Y Z))) := by gcongr
        _ ≤ 4 / lam * ((A * gradConstant S lam) * (2 * A * nearConstant S lam)) * S ^ 2 *
            (E * Real.exp (-(κ / 2 * D Y Z))) := by
            have : 0 ≤ E * Real.exp (-(κ / 2 * D Y Z)) := by positivity
            gcongr
        _ = _ := by ring
  have hsum : |∑ Z, ballCovariance r M Hv (freezeDefect (θ Z) e)| ≤
      4 / lam * ((A * gradConstant S lam) * (2 * A * nearConstant S lam)) * S ^ 2 * E * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun Z _ => hterm Z).trans ?_)
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left (hP.cell_sum_le le_rfl Y) (by positivity)
  have hq := abs_covariance_offBondsSq_le (M := M) (e := e) (Y := Y) hρ hr hmom hcov hκ hP hx hl hM hHs
    (h₁ := A * gradConstant S lam) (by positivity) hrr hsizeH hoff
  have hv := abs_expectation_obs_sub_freeze_le hρ hr hmom hκ hP hx hl hA0 hrr he hs hM hoff
  have hEq : Real.exp (-(κ * rr / 2)) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hEv : Real.exp (-(16 * κ * rr)) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
  have e1 : |ballCovariance r M Hv (offBondsSq e (x * lam / 2))| ≤
      4 / lam * (gradConstant S lam * squareConstant S lam) * S ^ 2 * (A ^ 2 * E) := by
    refine hq.trans ?_
    calc _ ≤ 4 / lam * (A * gradConstant S lam * squareConstant S lam) * S ^ 2 * E := by gcongr
      _ = 4 / lam * (gradConstant S lam * squareConstant S lam) * S ^ 2 * (A * E) := by ring
      _ ≤ _ := by gcongr
  have e2 : |ballExpectation r M (fun η => H η - H (freezeMap e η))| ≤ valueConstant S lam * S * (A ^ 2 * E) := by
    refine hv.trans ?_
    calc _ ≤ A * valueConstant S lam * S * E := by gcongr
      _ = valueConstant S lam * S * (A * E) := by ring
      _ ≤ _ := by gcongr
  have e3 : 4 / lam * ((A * gradConstant S lam) * (2 * A * nearConstant S lam)) * S ^ 2 * E * S =
      4 / lam * (gradConstant S lam * (2 * nearConstant S lam)) * S ^ 3 * (A ^ 2 * E) := by ring
  rw [e3] at hsum
  have habs := abs_sub (ballExpectation r M fun η => H η - H (freezeMap e η))
    ((∑ Z, ballCovariance r M Hv (freezeDefect (θ Z) e)) - ballCovariance r M Hv (offBondsSq e (x * lam / 2)))
  have habs2 := abs_sub (∑ Z, ballCovariance r M Hv (freezeDefect (θ Z) e))
    (ballCovariance r M Hv (offBondsSq e (x * lam / 2)))
  unfold sideConstant
  nlinarith
end Side
def quarticConstant (S lam : ℝ) : ℝ := 2 * (2 ^ 7 * S ^ 3 * (4 + 8 * S) / lam ^ 2 + 1)
def commonConstant (S lam : ℝ) : ℝ :=
  32 * S ^ 2 / lam + 1 + (4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 2 + quarticConstant S lam) +
    2 * (4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 3)
section Schwarz
variable {ι 𝒞 : Type} [Fintype ι] [DecidableEq ι] [Fintype 𝒞] [DecidableEq 𝒞] {ρ κ S lam x : ℝ}
  {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {M f g : BondField ι → ℝ}
theorem two_abs_covariance_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hM : Continuous M) (hf : Continuous f)
    (hg : Continuous g) {t : ℝ} (ht : 0 < t) :
    2 * |ballCovariance r M f g| ≤ t * ballCovariance r M f f + t⁻¹ * ballExpectation r M (fun η => g η ^ 2) := by
  set m := ballExpectation r M f with hm
  set n := ballExpectation r M g with hn
  have key : ∀ s : ℝ, 0 ≤ s ^ 2 * ballCovariance r M f f - 2 * s * (ballCovariance r M f g) +
      ballExpectation r M (fun η => g η ^ 2) - n ^ 2 := by
    intro s
    have h0 : 0 ≤ ballExpectation r M (fun η => (s * (f η - m) - (g η - n)) ^ 2) := by
      have := expectation_mono (f := fun _ => 0) (g := fun η => (s * (f η - m) - (g η - n)) ^ 2) hρ hr hM
        continuous_const (by fun_prop) (fun η _ => by positivity)
      rwa [expectation_const hρ hr hM] at this
    have e : (fun η => (s * (f η - m) - (g η - n)) ^ 2) = fun η =>
        (s ^ 2 * (f η * f η) + (-2 * s) * (f η * g η)) + ((g η ^ 2) +
          ((-2 * s ^ 2 * m + 2 * s * n) * f η + ((2 * s * m - 2 * n) * g η +
            (s ^ 2 * m ^ 2 - 2 * s * m * n + n ^ 2)))) := by
      funext η
      ring
    rw [e] at h0
    rw [expectation_add (f := fun η => s ^ 2 * (f η * f η) + (-2 * s) * (f η * g η)) hρ hr hM (by fun_prop)
      (by fun_prop), expectation_add (f := fun η => s ^ 2 * (f η * f η)) hρ hr hM (by fun_prop) (by fun_prop),
      expectation_add (f := fun η => g η ^ 2) hρ hr hM (by fun_prop) (by fun_prop),
      expectation_add (f := fun η => (-2 * s ^ 2 * m + 2 * s * n) * f η) hρ hr hM (by fun_prop) (by fun_prop),
      expectation_add (f := fun η => (2 * s * m - 2 * n) * g η) hρ hr hM (by fun_prop) continuous_const,
      expectation_const_mul, expectation_const_mul, expectation_const_mul, expectation_const_mul, expectation_const hρ hr hM,
      ← hm, ← hn] at h0
    unfold ballCovariance
    rw [← hm, ← hn]
    nlinarith [h0]
  have ht' : 0 < t⁻¹ := by positivity
  have hn2 : 0 ≤ t⁻¹ * n ^ 2 := by positivity
  have conv : ∀ c : ℝ, 0 ≤ t ^ 2 * ballCovariance r M f f - 2 * t * c + ballExpectation r M (fun η => g η ^ 2) - n ^ 2 →
      2 * c ≤ t * ballCovariance r M f f + t⁻¹ * ballExpectation r M (fun η => g η ^ 2) := fun c hc => by
    have h1 := mul_nonneg ht'.le hc
    have e1 : t⁻¹ * (t ^ 2 * ballCovariance r M f f - 2 * t * c + ballExpectation r M (fun η => g η ^ 2) - n ^ 2) =
        t * ballCovariance r M f f - 2 * c + t⁻¹ * ballExpectation r M (fun η => g η ^ 2) - t⁻¹ * n ^ 2 := by
      field_simp
    rw [e1] at h1
    linarith
  have k1 := conv _ (key t)
  have k2 := conv (-(ballCovariance r M f g)) (by
    have := key (-t)
    have e2 : (-t) ^ 2 = t ^ 2 := by ring
    rw [e2] at this
    linarith)
  rcases abs_cases (ballCovariance r M f g) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
theorem expectation_fourth_bond_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x) (hl : 0 < lam)
    {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (b : ι) :
    ballExpectation r Ψ (fun η => ‖η b‖ ^ 4) ≤ 2 ^ 7 * S * (4 + 8 * S) / (x * lam) ^ 2 := by
  obtain ⟨⟨K, hK⟩, s⟩ := hg
  have hm : 0 < x * lam / 4 := by positivity
  have hW : ∀ b₀, ∑ b, Real.exp (-(2 * κ * placementDist pl D b b₀)) ≤ S := fun b₀ => by
    have := hP.bond_sum_le hκ (μ := 2 * κ) (by linarith) (pl b₀)
    refine le_trans (le_of_eq ?_) this
    exact Finset.sum_congr rfl fun b _ => by rw [placementDist, hP.symm]
  have := hmom ι ρ (x * lam / 4) κ S (placementDist pl D) Ψ K r hρ hm hκ.le hr hP.pseudoMetric hK hW s 2 b
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero,
    mul_zero, zero_add, Nat.cast_one, mul_one, Nat.reduceMul] at this
  refine this.trans (le_of_eq ?_)
  field_simp
  ring
theorem expectation_weightedSq_sq_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r)
    (hmom : GaussianMomentBound) (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 0 < x)
    (hl : 0 < lam) {Ψ : BondField ι → ℝ} (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (Z : 𝒞) :
    x ^ 2 * ballExpectation r Ψ (fun η => weightedSqNormAt κ pl D Z η ^ 2) ≤ 2 ^ 7 * S ^ 3 * (4 + 8 * S) / lam ^ 2 := by
  have hΨ := hg.continuous_potential
  have hS : 0 ≤ S := hP.const_nonneg Z
  set w : ι → ℝ := fun b => Real.exp (-(2 ^ 6 * κ * D Z (pl b))) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have hsumw : ∑ b, w b ≤ S := hP.bond_sum_le hκ (by nlinarith) Z
  have hsq := weightedSq_continuous (κ := κ) (pl := pl) (D := D) (ι := ι) Z
  have hpoint : ∀ η ∈ openPolyball ι ρ, weightedSqNormAt κ pl D Z η ^ 2 ≤ S * ∑ b, w b * ‖η b‖ ^ 4 := fun η _ => by
    have h1 : (∑ b, w b * ‖η b‖ ^ 2) ^ 2 ≤ (∑ b, w b) * ∑ b, w b * ‖η b‖ ^ 4 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun b _ => hw0 b)
        (fun b _ => mul_nonneg (hw0 b) (by positivity)) (fun b _ => by ring)
    have h2 : 0 ≤ ∑ b, w b * ‖η b‖ ^ 4 :=
      Finset.sum_nonneg fun b _ => mul_nonneg (hw0 b) (by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_right hsumw h2)
  have h3 := expectation_mono (f := fun η => weightedSqNormAt κ pl D Z η ^ 2)
    (g := fun η => S * ∑ b, w b * ‖η b‖ ^ 4) hρ hr hΨ (by fun_prop)
    (continuous_const.mul (continuous_finset_sum _ fun b _ => by fun_prop)) hpoint
  rw [expectation_const_mul, expectation_sum _ _ hρ hr hΨ (fun b _ => by fun_prop)] at h3
  have h4 : ∑ b, ballExpectation r Ψ (fun η => w b * ‖η b‖ ^ 4) ≤ S * (2 ^ 7 * S * (4 + 8 * S) / (x * lam) ^ 2) := by
    calc _ = ∑ b, w b * ballExpectation r Ψ (fun η => ‖η b‖ ^ 4) :=
          Finset.sum_congr rfl fun b _ => expectation_const_mul _
      _ ≤ ∑ b, w b * (2 ^ 7 * S * (4 + 8 * S) / (x * lam) ^ 2) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (expectation_fourth_bond_le hρ hr hmom hκ hP hx hl hg b) (hw0 b)
      _ = (∑ b, w b) * (2 ^ 7 * S * (4 + 8 * S) / (x * lam) ^ 2) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsumw (by positivity)
  calc _ ≤ x ^ 2 * (S * (S * (2 ^ 7 * S * (4 + 8 * S) / (x * lam) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact h3.trans (mul_le_mul_of_nonneg_left h4 hS)
    _ = _ := by
        field_simp
end Schwarz
section Common
variable {Λ ι ι' 𝒞 𝒞' 𝒩 : Type} [Fintype Λ] [DecidableEq Λ] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι'] [Fintype 𝒞] [DecidableEq 𝒞] [Fintype 𝒞'] [DecidableEq 𝒞']
  [Fintype 𝒩] [DecidableEq 𝒩]
  {ρ κ S lam x A ε rad : ℝ} {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {e : Λ → ι}
  {pl' : ι' → 𝒞'} {D' : 𝒞' → 𝒞' → ℝ} {e' : Λ → ι'} {n : 𝒩 → 𝒞} {n' : 𝒩 → 𝒞'}
  {θ : 𝒞 → BondField ι → ℝ} {Ψ H : BondField ι → ℝ} {Y : 𝒞}
  {θ' : 𝒞' → BondField ι' → ℝ} {Ψ' H' : BondField ι' → ℝ} {Y' : 𝒞'}
theorem weightedSq_zeroExtension (he : Function.Injective e) (Z : 𝒞) (ζ : BondField Λ) :
    weightedSqNormAt κ pl D Z (zeroExtensionL e ζ) = weightedSqNormAt κ (pl ∘ e) D Z ζ := by
  unfold weightedSqNormAt
  rw [sum_eq_sum_comp_of_vanish he _ (fun b hb => by rw [zeroExtension_apply_off hb]; simp)]
  exact Finset.sum_congr rfl fun l _ => by rw [zeroExtension_apply_self he]; rfl
theorem placement_comp (he : Function.Injective e) (hP : IsDecayingPlacement κ S pl D) :
    IsDecayingPlacement κ S (pl ∘ e) D :=
  ⟨hP.self, hP.symm, hP.triangle, fun Z => (sum_comp_le_sum_of_nonneg he
    (fun b => Real.exp (-(κ / 2 * D Z (pl b)))) fun _ => (Real.exp_pos _).le).trans (hP.bonds Z), hP.cells⟩
theorem sum_eq_sum_range_add_offBonds (hn : Function.Injective n) (f : 𝒞 → ℝ) :
    ∑ Z, f Z = ∑ j, f (n j) + ∑ Z ∈ offBonds n, f Z := by
  classical
  have h1 := sum_eq_sum_comp_of_vanish hn (fun Z => if Z ∈ Set.range n then f Z else 0)
    (fun Z hZ => by simp [hZ])
  have h2 : ∀ j, (if n j ∈ Set.range n then f (n j) else 0) = f (n j) := fun j => by
    rw [if_pos ⟨j, rfl⟩]
  simp only [h2] at h1
  rw [← h1, offBonds, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Z _ => ?_
  by_cases hZ : Z ∈ Set.range n <;> simp [hZ]
section Term
variable {M : BondField Λ → ℝ}
theorem l2Norm_gradNorm_term_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A)
    (he : Function.Injective e) (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y)
    (hM : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist (pl ∘ e) D) M) (Z : 𝒞) (l : Λ) :
    ballL2Norm r M (bondGradNorm (fun ζ => θ Z (zeroExtensionL e ζ)) l) ≤
      (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 * κ * D Z (pl (e l)))) := by
  have hPΛ := placement_comp he hP
  have hsm : ContDiff ℝ 1 (fun ζ => θ Z (zeroExtensionL e ζ)) :=
    ((hs.smooth Z).of_le (by norm_num) : ContDiff ℝ 1 (θ Z)).comp (zeroExtensionL e).contDiff
  have := l2Norm_le_of_linear_growth hρ hr hmom hκ hPΛ hx hl hM Z (continuous_gradNorm hsm l)
    (gradNorm_nonneg _ _) (a := A * Real.exp (-(2 ^ 5 * κ * D Z (pl (e l))))) (by positivity)
    (fun ζ hζ => by
      rw [gradNorm_zeroExtension he (hs.term_diff Z)]
      refine (hs.slope Z _ (zeroExtension_mem_polyball hρ he hζ) _).trans (le_of_eq ?_)
      rw [weightedSq_zeroExtension he]
      ring)
  refine this.trans ?_
  have h2 := exp_neg_le_of_rate (hP.dist_nonneg Z (pl (e l))) (a := 2 * κ) (b := 2 ^ 5 * κ) (by nlinarith)
  have h3 := gradConstant_nonneg S lam
  calc _ = (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 ^ 5 * κ * D Z (pl (e l)))) := by ring
    _ ≤ _ := by gcongr
end Term
theorem final_triangle_bound {a b k P Q Nc u v w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) (hN : 0 ≤ Nc) (hu : |u| ≤ a * Q) (hv : |v| ≤ b * (Q * Nc)) (hw : |w| ≤ k * P)
    (hz : |z| ≤ k * P) :
    |u - ((v + w) - z)| ≤ (a + b + 2 * k) * (P + Q * (1 + Nc)) := by
  have h1 := abs_sub u ((v + w) - z)
  have h2 := abs_sub (v + w) z
  have h3 := abs_add_le v w
  have e6 : 0 ≤ a * P + a * (Q * Nc) + b * P + b * Q + 2 * k * (Q * (1 + Nc)) := by positivity
  linarith
set_option maxHeartbeats 800000 in
theorem abs_expectation_common_sub_le (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hseg : MeanDifferenceBoundAlongSegment)
    (hmom : GaussianMomentBound) (hcov : CovarianceBoundHolds ρ r)
    (hκ : 0 < κ) (hP : IsDecayingPlacement κ S pl D) (hP' : IsDecayingPlacement κ S pl' D') (hx : 1 ≤ x) (hl : 0 < lam)
    (hA : 1 ≤ A) (hε : 0 < ε) (hrad : 0 ≤ rad) (he : Function.Injective e)
    (he' : Function.Injective e') (hn : Function.Injective n) (hn' : Function.Injective n')
    (hD : ∀ l l', D (pl (e l)) (pl (e l')) = D' (pl' (e' l)) (pl' (e' l')))
    (hDY : ∀ l, D Y (pl (e l)) = D' Y' (pl' (e' l)))
    (hfar : ∀ Z, Z ∉ Set.range n → rad / 8 ≤ D Y Z) (hfar' : ∀ Z, Z ∉ Set.range n' → rad / 8 ≤ D' Y' Z)
    (hΨ : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ)
    (hΨ' : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl' D') Ψ')
    (hs : IsLocalDecomposition ρ x κ A pl D θ Ψ H Y) (hs' : IsLocalDecomposition ρ x κ A pl' D' θ' Ψ' H' Y')
    (hc : IsCloseInValue ρ x κ ε pl D e e' n n' θ θ' H H' Y) :
    |ballExpectation r (fun ζ => Ψ (zeroExtensionL e ζ)) (fun ζ => H (zeroExtensionL e ζ)) -
        ballExpectation r (fun ζ => Ψ' (zeroExtensionL e' ζ)) (fun ζ => H' (zeroExtensionL e' ζ))| ≤
      commonConstant S lam * (A ^ 2 * Real.exp (-(κ * rad / 2 ^ 4)) + A * ε * (1 + Fintype.card 𝒩)) := by
  have hx0 : 0 < x := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hS1 : 1 ≤ S := hP.one_le_const Y
  have hc0 := gradConstant_nonneg S lam
  have hm : 0 < x * lam / 4 := by positivity
  have hPΛ := placement_comp he hP
  have hPΛ' := placement_comp he' hP'
  set G : BondField Λ → ℝ := fun ζ => Ψ (zeroExtensionL e ζ) with hG
  set G' : BondField Λ → ℝ := fun ζ => Ψ' (zeroExtensionL e' ζ) with hG'
  set h : BondField Λ → ℝ := fun ζ => H (zeroExtensionL e ζ) with hh
  set h' : BondField Λ → ℝ := fun ζ => H' (zeroExtensionL e' ζ) with hh'
  have hdist : placementDist (pl' ∘ e') D' = placementDist (pl ∘ e) D := by
    funext l l'
    exact (hD l l').symm
  have gG : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist (pl ∘ e) D) G :=
    hΨ.pullback hρ hκ.le he hP.pseudoMetric
  have gG' : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist (pl ∘ e) D) G' := by
    rw [← hdist]
    exact hΨ'.pullback hρ hκ.le he' hP'.pseudoMetric
  have hhs : ContDiff ℝ 1 h := hs.smooth_obs.comp (zeroExtensionL e).contDiff
  have hhs' : ContDiff ℝ 1 h' := hs'.smooth_obs.comp (zeroExtensionL e').contDiff
  have hhd : Differentiable ℝ h := hhs.differentiable (by simp)
  have hhd' : Differentiable ℝ h' := hhs'.differentiable (by simp)
  obtain ⟨Mb, hMb⟩ := exists_common_bound_polyball hρ gG'.continuous_potential gG.continuous_potential hhs'.continuous hhs.continuous
  set E := Real.exp (-(κ * rad / 2 ^ 4)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  refine (hseg Λ ρ r G' G h' h Mb _ hρ hr gG'.continuous_potential.continuousOn gG.continuous_potential.continuousOn
    hhs'.continuous.continuousOn hhs.continuous.continuousOn hMb fun v h0 h1 => ?_)
  have hM := gG'.interpolate hm gG h0 h1
  have hMc := hM.continuous_potential
  set M := segmentInterpolant G' G v with hMdef
  have hM' : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist (pl' ∘ e') D') M := by
    rw [hdist]
    exact hM
  set Hv := segmentInterpolant h' h v with hHv
  have hHs : ContDiff ℝ 1 Hv := (contDiff_const.mul hhs).add (contDiff_const.mul hhs')
  have hsq : ∀ ζ : BondField Λ, weightedSqNormAt κ pl' D' Y' (zeroExtensionL e' ζ) =
      weightedSqNormAt κ pl D Y (zeroExtensionL e ζ) := fun ζ => by
    rw [weightedSq_zeroExtension he', weightedSq_zeroExtension he]
    unfold weightedSqNormAt
    exact Finset.sum_congr rfl fun l _ => by
      simp only [Function.comp_apply, hDY l]
  have hsz : ∀ l, ballL2Norm r M (bondGradNorm Hv l) ≤
      (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 * κ * D Y (pl (e l)))) := fun l => by
    have := l2Norm_le_of_linear_growth hρ hr hmom hκ hPΛ hx hl hM Y (continuous_gradNorm hHs l)
      (gradNorm_nonneg _ _) (a := A * Real.exp (-(2 ^ 5 * κ * D Y (pl (e l))))) (by positivity)
      (fun ζ hζ => by
        have e1 : bondGradNorm h l ζ ≤ A * Real.exp (-(2 ^ 5 * κ * D Y (pl (e l)))) *
            (x * Real.sqrt (weightedSqNormAt κ (pl ∘ e) D Y ζ) + 1) := by
          rw [hh, gradNorm_zeroExtension he hs.obs_diff]
          refine (hs.slope_obs _ (zeroExtension_mem_polyball hρ he hζ) _).trans (le_of_eq ?_)
          rw [weightedSq_zeroExtension he]
          ring
        have e2 : bondGradNorm h' l ζ ≤ A * Real.exp (-(2 ^ 5 * κ * D Y (pl (e l)))) *
            (x * Real.sqrt (weightedSqNormAt κ (pl ∘ e) D Y ζ) + 1) := by
          rw [hh', gradNorm_zeroExtension he' hs'.obs_diff]
          refine (hs'.slope_obs _ (zeroExtension_mem_polyball hρ he' hζ) _).trans (le_of_eq ?_)
          rw [hsq, weightedSq_zeroExtension he, ← hDY]
          ring
        exact gradNorm_segment_le hhd' hhd h0 h1 l ζ e2 e1)
    refine this.trans ?_
    have h2 := exp_neg_le_of_rate (hP.dist_nonneg Y (pl (e l))) (a := 2 * κ) (b := 2 ^ 5 * κ) (by nlinarith)
    calc _ = (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 ^ 5 * κ * D Y (pl (e l)))) := by ring
      _ ≤ _ := by gcongr
  have hsz' : ∀ l, ballL2Norm r M (bondGradNorm Hv l) ≤
      (A * gradConstant S lam) * Real.sqrt x * Real.exp (-(2 * κ * D' Y' ((pl' ∘ e') l))) := fun l => by
    have := hsz l
    rwa [hDY l] at this
  set Gj : 𝒩 → BondField Λ → ℝ := fun j ζ => θ (n j) (zeroExtensionL e ζ) - θ' (n' j) (zeroExtensionL e' ζ) with hGj
  have hθs : ∀ Z, ContDiff ℝ 1 (fun ζ => θ Z (zeroExtensionL e ζ)) := fun Z =>
    ((hs.smooth Z).of_le (by norm_num) : ContDiff ℝ 1 (θ Z)).comp (zeroExtensionL e).contDiff
  have hθs' : ∀ Z, ContDiff ℝ 1 (fun ζ => θ' Z (zeroExtensionL e' ζ)) := fun Z =>
    ((hs'.smooth Z).of_le (by norm_num) : ContDiff ℝ 1 (θ' Z)).comp (zeroExtensionL e').contDiff
  have hGjs : ∀ j, ContDiff ℝ 1 (Gj j) := fun j => (hθs _).sub (hθs' _)
  have hcg : ballCovariance r M Hv (fun ζ => G ζ - G' ζ) =
      (∑ j, ballCovariance r M Hv (Gj j)) + (∑ Z ∈ offBonds n, ballCovariance r M Hv (fun ζ => θ Z (zeroExtensionL e ζ))) -
        ∑ Z ∈ offBonds n', ballCovariance r M Hv (fun ζ => θ' Z (zeroExtensionL e' ζ)) := by
    rw [covariance_congr (g' := fun ζ => ((∑ j, Gj j ζ) + ∑ Z ∈ offBonds n, θ Z (zeroExtensionL e ζ)) -
      ∑ Z ∈ offBonds n', θ' Z (zeroExtensionL e' ζ)) hr (fun _ _ => rfl) (fun _ _ => rfl) (fun ζ hζ => ?_),
      covariance_sub (g := fun ζ => (∑ j, Gj j ζ) + ∑ Z ∈ offBonds n, θ Z (zeroExtensionL e ζ)) hρ hr hMc hHs.continuous
        ((continuous_finset_sum _ fun j _ => (hGjs j).continuous).add
          (continuous_finset_sum _ fun Z _ => (hθs Z).continuous))
        (continuous_finset_sum _ fun Z _ => (hθs' Z).continuous),
      covariance_add (g := fun ζ => ∑ j, Gj j ζ) hρ hr hMc hHs.continuous
        (continuous_finset_sum _ fun j _ => (hGjs j).continuous)
        (continuous_finset_sum _ fun Z _ => (hθs Z).continuous),
      covariance_sum _ _ hρ hr hMc hHs.continuous fun j _ => (hGjs j).continuous,
      covariance_sum _ _ hρ hr hMc hHs.continuous fun Z _ => (hθs Z).continuous,
      covariance_sum _ _ hρ hr hMc hHs.continuous fun Z _ => (hθs' Z).continuous]
    have e1 := hs.sum _ (zeroExtension_mem_polyball hρ he hζ)
    have e2 := hs'.sum _ (zeroExtension_mem_polyball hρ he' hζ)
    have e3 := sum_eq_sum_range_add_offBonds hn (fun Z => θ Z (zeroExtensionL e ζ))
    have e4 := sum_eq_sum_range_add_offBonds hn' (fun Z => θ' Z (zeroExtensionL e' ζ))
    simp only [hG, hG', hGj, e1, e2, e3, e4, Finset.sum_sub_distrib]
    ring
  rw [hcg]
  set K₀ := 4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 2 with hK₀
  have hc4 : 0 ≤ quarticConstant S lam := by unfold quarticConstant; positivity
  have hvar : ballCovariance r M Hv Hv ≤ K₀ * A ^ 2 := by
    have h1 := abs_covariance_le_localized hcov hκ hPΛ hx0 hl hM hHs hHs (h₁ := A * gradConstant S lam) (h₂ := A * gradConstant S lam)
      (by positivity) (by positivity) Y Y hsz hsz
    rw [hP.self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    refine (le_abs_self _).trans (h1.trans (le_of_eq ?_))
    rw [hK₀]
    ring
  have hG2 : ∀ j, ballExpectation r M (fun ζ => Gj j ζ ^ 2) ≤ ε ^ 2 * quarticConstant S lam := fun j => by
    have hsqc := weightedSq_continuous (κ := κ) (pl := pl ∘ e) (D := D) (ι := Λ) (n j)
    have hpoint : ∀ ζ ∈ openPolyball Λ ρ, Gj j ζ ^ 2 ≤
        ε ^ 2 * ((2 * x ^ 2) * weightedSqNormAt κ (pl ∘ e) D (n j) ζ ^ 2 + 2) := fun ζ hζ => by
      have h1 := hc.terms j ζ hζ
      rw [weightedSq_zeroExtension he] at h1
      have h2 : 0 ≤ weightedSqNormAt κ (pl ∘ e) D (n j) ζ := weightedSq_nonneg _ _
      set u := weightedSqNormAt κ (pl ∘ e) D (n j) ζ
      have h3 : Gj j ζ ^ 2 ≤ (ε * (x * u + 1)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      refine h3.trans ?_
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg (x * u - 1)]
    have h4 := expectation_mono (f := fun ζ => Gj j ζ ^ 2)
      (g := fun ζ => ε ^ 2 * ((2 * x ^ 2) * weightedSqNormAt κ (pl ∘ e) D (n j) ζ ^ 2 + 2)) hρ hr hMc
      (by have := (hGjs j).continuous; fun_prop) (by fun_prop) hpoint
    refine h4.trans ?_
    rw [expectation_const_mul, expectation_add (f := fun ζ => (2 * x ^ 2) * weightedSqNormAt κ (pl ∘ e) D (n j) ζ ^ 2)
      (g := fun _ => 2) hρ hr hMc (by fun_prop) continuous_const, expectation_const_mul, expectation_const hρ hr hMc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h5 := expectation_weightedSq_sq_le hρ hr hmom hκ hPΛ hx0 hl hM (n j)
    unfold quarticConstant
    linarith
  have hAε : 0 < A * ε := by positivity
  have hcmp : |∑ j, ballCovariance r M Hv (Gj j)| ≤ (K₀ + quarticConstant S lam) * (A * ε * Fintype.card 𝒩) := by
    have hterm : ∀ j, |ballCovariance r M Hv (Gj j)| ≤ (K₀ + quarticConstant S lam) * (A * ε) := fun j => by
      have ht : 0 < ε / A := by positivity
      have h1 := two_abs_covariance_le hρ hr hMc hHs.continuous (hGjs j).continuous ht
      have h2 : ε / A * ballCovariance r M Hv Hv ≤ ε / A * (K₀ * A ^ 2) :=
        mul_le_mul_of_nonneg_left hvar ht.le
      have h3 : (ε / A)⁻¹ * ballExpectation r M (fun ζ => Gj j ζ ^ 2) ≤ (ε / A)⁻¹ * (ε ^ 2 * quarticConstant S lam) :=
        mul_le_mul_of_nonneg_left (hG2 j) (by positivity)
      have e1 : ε / A * (K₀ * A ^ 2) = K₀ * (A * ε) := by field_simp
      have e2 : (ε / A)⁻¹ * (ε ^ 2 * quarticConstant S lam) = quarticConstant S lam * (A * ε) := by field_simp
      rw [e1] at h2
      rw [e2] at h3
      have h4 : 0 ≤ |ballCovariance r M Hv (Gj j)| := abs_nonneg _
      nlinarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hterm j).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply le_of_eq
    ring
  have hfarsum : ∀ {𝒟 : Type} [Fintype 𝒟] [DecidableEq 𝒟] {Δ : 𝒟 → 𝒟 → ℝ} {y : 𝒟} (T : Finset 𝒟),
      (∀ Z ∈ T, rad / 8 ≤ Δ y Z) → (∀ Z, 0 ≤ Δ y Z) →
      (∑ Z, Real.exp (-(κ / 2 * Δ y Z)) ≤ S) → ∑ Z ∈ T, Real.exp (-(κ * Δ y Z)) ≤ E * S := by
    intro 𝒟 _ _ Δ y T hT h0' hsum
    calc _ ≤ ∑ Z ∈ T, E * Real.exp (-(κ / 2 * Δ y Z)) := by
          refine Finset.sum_le_sum fun Z hZ => ?_
          rw [hE, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := hT Z hZ
          nlinarith
      _ = E * ∑ Z ∈ T, Real.exp (-(κ / 2 * Δ y Z)) := by rw [Finset.mul_sum]
      _ ≤ E * ∑ Z, Real.exp (-(κ / 2 * Δ y Z)) := by
          apply mul_le_mul_of_nonneg_left _ hE0
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hE0
  have hf1 : |∑ Z ∈ offBonds n, ballCovariance r M Hv (fun ζ => θ Z (zeroExtensionL e ζ))| ≤
      4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 3 * (A ^ 2 * E) := by
    have hterm : ∀ Z, |ballCovariance r M Hv (fun ζ => θ Z (zeroExtensionL e ζ))| ≤
        4 / lam * ((A * gradConstant S lam) * (A * gradConstant S lam)) * S ^ 2 * Real.exp (-(κ * D Y Z)) := fun Z =>
      abs_covariance_le_localized hcov hκ hPΛ hx0 hl hM hHs (hθs Z) (by positivity) (by positivity) Y Z hsz
        (l2Norm_gradNorm_term_le hρ hr hmom hκ hP hx hl hA0 he hs hM Z)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun Z _ => hterm Z).trans ?_)
    rw [← Finset.mul_sum]
    have h1 := hfarsum (Δ := D) (y := Y) (offBonds n) (fun Z hZ => hfar Z (mem_offBonds.mp hZ))
      (hP.dist_nonneg Y) (hP.cell_sum_le le_rfl Y)
    calc _ ≤ 4 / lam * ((A * gradConstant S lam) * (A * gradConstant S lam)) * S ^ 2 * (E * S) := by gcongr
      _ = _ := by ring
  have hf2 : |∑ Z ∈ offBonds n', ballCovariance r M Hv (fun ζ => θ' Z (zeroExtensionL e' ζ))| ≤
      4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 3 * (A ^ 2 * E) := by
    have hterm : ∀ Z, |ballCovariance r M Hv (fun ζ => θ' Z (zeroExtensionL e' ζ))| ≤
        4 / lam * ((A * gradConstant S lam) * (A * gradConstant S lam)) * S ^ 2 * Real.exp (-(κ * D' Y' Z)) := fun Z =>
      abs_covariance_le_localized hcov hκ hPΛ' hx0 hl hM' hHs (hθs' Z) (by positivity) (by positivity) Y' Z hsz'
        (l2Norm_gradNorm_term_le hρ hr hmom hκ hP' hx hl hA0 he' hs' hM' Z)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun Z _ => hterm Z).trans ?_)
    rw [← Finset.mul_sum]
    have h1 := hfarsum (Δ := D') (y := Y') (offBonds n') (fun Z hZ => hfar' Z (mem_offBonds.mp hZ))
      (hP'.dist_nonneg Y') (hP'.cell_sum_le le_rfl Y')
    calc _ ≤ 4 / lam * ((A * gradConstant S lam) * (A * gradConstant S lam)) * S ^ 2 * (E * S) := by gcongr
      _ = _ := by ring
  have hval : |ballExpectation r M (fun ζ => h ζ - h' ζ)| ≤ (32 * S ^ 2 / lam + 1) * (A * ε) := by
    have hsqc := weightedSq_continuous (κ := κ) (pl := pl ∘ e) (D := D) (ι := Λ) Y
    have h1 := abs_expectation_le (f := fun ζ => h ζ - h' ζ)
      (g := fun ζ => ε * (x * weightedSqNormAt κ (pl ∘ e) D Y ζ + 1)) hρ hr hMc
      (hhs.continuous.sub hhs'.continuous) (by fun_prop)
      (fun ζ hζ => by
        have := hc.value ζ hζ
        rwa [weightedSq_zeroExtension he] at this)
    refine h1.trans ?_
    rw [expectation_const_mul, show (fun ζ => x * weightedSqNormAt κ (pl ∘ e) D Y ζ + 1) =
      fun ζ => x * weightedSqNormAt κ (pl ∘ e) D Y ζ + 1 from rfl,
      expectation_add (f := fun ζ => x * weightedSqNormAt κ (pl ∘ e) D Y ζ) (g := fun _ => 1) hρ hr hMc
        (by fun_prop) continuous_const, expectation_const_mul, expectation_const hρ hr hMc]
    have h2 := expectation_weightedSq_le hρ hr hmom hκ hPΛ hx0 hl hM Y
    have h3 : x * ballExpectation r M (weightedSqNormAt κ (pl ∘ e) D Y) ≤ 32 * S ^ 2 / lam := by
      calc _ ≤ x * (S * (32 * S / (x * lam))) := mul_le_mul_of_nonneg_left h2 hx0.le
        _ = _ := by field_simp
    have h4 : 0 ≤ 32 * S ^ 2 / lam + 1 := by positivity
    calc _ ≤ ε * (32 * S ^ 2 / lam + 1) := by gcongr
      _ ≤ A * ε * (32 * S ^ 2 / lam + 1) := by
          apply mul_le_mul_of_nonneg_right _ h4
          have := mul_le_mul_of_nonneg_right hA hε.le
          linarith
      _ = _ := by ring
  have hk1 : 0 ≤ 4 / lam * (gradConstant S lam * gradConstant S lam) * S ^ 3 := by positivity
  have hk2 : 0 ≤ 32 * S ^ 2 / lam + 1 := by positivity
  have hAE : 0 ≤ A ^ 2 * E := by positivity
  have hNc : (0 : ℝ) ≤ ((Fintype.card 𝒩 : ℕ) : ℝ) := by positivity
  have hb0 : 0 ≤ K₀ + quarticConstant S lam := by positivity
  have hfin := final_triangle_bound hk2 hb0 hk1 hAE hAε.le hNc hval (by rwa [mul_assoc] at hcmp) hf1 hf2
  refine hfin.trans (le_of_eq ?_)
  simp only [commonConstant, hK₀, mul_assoc]
end Common
theorem abs_expectation_le_of_growth {ι 𝒞 : Type} [Fintype ι] [DecidableEq ι] [Fintype 𝒞] [DecidableEq 𝒞]
    {ρ x κ A S lam : ℝ} {r : ℝ → ℝ} {pl : ι → 𝒞} {D : 𝒞 → 𝒞 → ℝ} {Ψ H : BondField ι → ℝ} {Y : 𝒞}
    (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) (hmom : GaussianMomentBound) (hκ : 0 < κ)
    (hP : IsDecayingPlacement κ S pl D) (hx : 1 ≤ x) (hl : 0 < lam) (hA : 0 ≤ A)
    (hg : IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ) (hH : Continuous H)
    (hb : ∀ η ∈ openPolyball ι ρ, |H η| ≤ A * (x * weightedSqNormAt κ pl D Y η + 1)) :
    |ballExpectation r Ψ H| ≤ (32 * S ^ 2 / lam + 1) * A := by
  have hx0 : 0 < x := by linarith
  have hMc := hg.continuous_potential
  have hsqc := weightedSq_continuous (κ := κ) (pl := pl) (D := D) (ι := ι) Y
  refine (abs_expectation_le hρ hr hMc hH (by fun_prop) hb).trans ?_
  rw [expectation_const_mul, expectation_add (f := fun η => x * weightedSqNormAt κ pl D Y η) (g := fun _ => 1) hρ hr hMc
    (by fun_prop) continuous_const, expectation_const_mul, expectation_const hρ hr hMc]
  have h2 := expectation_weightedSq_le hρ hr hmom hκ hP hx0 hl hg Y
  have h3 : x * ballExpectation r Ψ (weightedSqNormAt κ pl D Y) ≤ 32 * S ^ 2 / lam := by
    calc _ ≤ x * (S * (32 * S / (x * lam))) := mul_le_mul_of_nonneg_left h2 hx0.le
      _ = _ := by field_simp
  calc _ ≤ A * (32 * S ^ 2 / lam + 1) := by gcongr
    _ = _ := by ring
end ValueFreezing
open ValueFreezing in
theorem expectationsAgreeInValue_of_lemmas (h₁ : MeanDifferenceBoundAlongSegment)
    (h₂ : GaussianMomentBound) (h₃ : BallCovarianceBound)
    (h₄ : CutoffFactorIsRadialCutoff) : ExpectationsAgreeInValue := by
  intro S lam hl
  have hC : ∀ (ρ : ℝ) (p : ℝ → ℝ) (α : Type) [Fintype α] (G f : BondField α → ℝ),
      ballExpectation (fun u => cutoffFactor ρ p (max u 0)) G f = ballExpectation (cutoffFactor ρ p) G f := by
    intro ρ p α _ G f
    have hdens : ballDensity (fun u => cutoffFactor ρ p (max u 0)) G = ballDensity (cutoffFactor ρ p) G := by
      funext η
      simp [ballDensity, radialWeightProd, max_eq_left (norm_nonneg _)]
    unfold ballExpectation
    rw [hdens]
  refine ⟨max (32 * S ^ 2 / lam + 1) (2 * sideConstant S lam + commonConstant S lam), ?_, ?_⟩
  · intro ι 𝒞 _ _ _ _ ρ x κ A p pl D Ψ H Y hρ hp hκ hx hA hP hg hH hb
    rw [← hC]
    exact (abs_expectation_le_of_growth hρ (h₄ ρ p hρ hp) h₂ hκ hP hx hl hA hg hH hb).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
  intro ι ι' 𝒞 𝒞' Λ 𝒩 _ _ _ _ _ _ _ _ _ _ _ _ ρ x κ A ε rad p pl D pl' D' e e' n n' θ θ' Ψ H Ψ' H' Y Y'
    hρ hp hκ hx hA hε hrad hP hP' he he' hn hn' hD hDY hoff hoff' hfar hfar' hΨ hΨ' hs hs' hc
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hrdef
  have hr : IsRadialCutoff ρ r := h₄ ρ p hρ hp
  have hdens : ∀ (α : Type) [Fintype α] (G : BondField α → ℝ),
      ballDensity r G = ballDensity (cutoffFactor ρ p) G := fun α _ G => by
    funext η
    simp [ballDensity, radialWeightProd, hrdef, max_eq_left (norm_nonneg _)]
  have hmean : ∀ (α : Type) [Fintype α] (G f : BondField α → ℝ),
      ballExpectation r G f = ballExpectation (cutoffFactor ρ p) G f := fun α _ G f => by
    unfold ballExpectation
    rw [hdens]
  have hcov : CovarianceBoundHolds ρ r := by
    intro α _ _ m κ' d G K hm hκ' hd hK f g hf hg
    have := h₃ α ρ m κ' d G K p hρ hm hκ' hp hd hK f g hf hg
    simpa only [ballCovariance, ballL2Norm, hmean] using this
  rw [← hmean, ← hmean]
  have hS1 : 1 ≤ S := hP.one_le_const Y
  have hS : 0 ≤ S := by linarith
  have hrr : 0 ≤ rad / 2 := by positivity
  have s1 := abs_expectation_sub_frozen_le (rr := rad / 2) hρ hr h₁ h₂ hcov hκ hP hx hl hA hrr he hs hΨ hoff
  have s2 := abs_expectation_sub_frozen_le (rr := rad / 2) hρ hr h₁ h₂ hcov hκ hP' hx hl hA hrr he' hs' hΨ' hoff'
  have s3 := abs_expectation_common_sub_le hρ hr h₁ h₂ hcov hκ hP hP' hx hl hA hε hrad he he' hn hn' hD hDY hfar hfar'
    hΨ hΨ' hs hs' hc
  have m1 : ballExpectation r (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ e (x * lam / 2)) (fun η => H (freezeMap e η)) =
      ballExpectation r (fun ζ => Ψ (zeroExtensionL e ζ)) (fun ζ => H (zeroExtensionL e ζ)) :=
    expectation_frozen hρ hr he (G := fun ζ => Ψ (zeroExtensionL e ζ)) (h := fun ζ => H (zeroExtensionL e ζ)) _
  have m2 : ballExpectation r (_root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.frozenPotential Ψ' e' (x * lam / 2)) (fun η => H' (freezeMap e' η)) =
      ballExpectation r (fun ζ => Ψ' (zeroExtensionL e' ζ)) (fun ζ => H' (zeroExtensionL e' ζ)) :=
    expectation_frozen hρ hr he' (G := fun ζ => Ψ' (zeroExtensionL e' ζ)) (h := fun ζ => H' (zeroExtensionL e' ζ)) _
  rw [m1] at s1
  rw [m2] at s2
  set E := Real.exp (-(κ * rad / 2 ^ 4)) with hE
  have hE8 : Real.exp (-(κ * (rad / 2) / 4)) ≤ E := by
    rw [hE]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ κ * rad := by positivity
    nlinarith
  have hcs : 0 ≤ sideConstant S lam := by
    unfold sideConstant
    have := gradConstant_nonneg S lam
    have := nearConstant_nonneg (S := S) (lam := lam) hS
    have : 0 ≤ squareConstant S lam := Real.sqrt_nonneg _
    have : 0 ≤ valueConstant S lam := by unfold valueConstant; positivity
    positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hAe : 0 ≤ A * ε * (1 + Fintype.card 𝒩) := by positivity
  have hs1 : sideConstant S lam * (A ^ 2 * Real.exp (-(κ * (rad / 2) / 4))) ≤ sideConstant S lam * (A ^ 2 * E) := by
    gcongr
  have t1 := abs_sub_le (ballExpectation r Ψ H) (ballExpectation r (fun ζ => Ψ (zeroExtensionL e ζ)) (fun ζ => H (zeroExtensionL e ζ)))
    (ballExpectation r Ψ' H')
  have t2 := abs_sub_le (ballExpectation r (fun ζ => Ψ (zeroExtensionL e ζ)) (fun ζ => H (zeroExtensionL e ζ)))
    (ballExpectation r (fun ζ => Ψ' (zeroExtensionL e' ζ)) (fun ζ => H' (zeroExtensionL e' ζ))) (ballExpectation r Ψ' H')
  rw [abs_sub_comm (ballExpectation r (fun ζ => Ψ' (zeroExtensionL e' ζ)) (fun ζ => H' (zeroExtensionL e' ζ)))] at t2
  have hA2 : 0 ≤ A ^ 2 * E := by positivity
  have hfin : |ballExpectation r Ψ H - ballExpectation r Ψ' H'| ≤
      (2 * sideConstant S lam + commonConstant S lam) * (A ^ 2 * E + A * ε * (1 + Fintype.card 𝒩)) := by
    have e7 : sideConstant S lam * (A ^ 2 * E) ≤ sideConstant S lam * (A ^ 2 * E + A * ε * (1 + Fintype.card 𝒩)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcs
    nlinarith
  exact hfin.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
end YangMills.Construction.ColdStepAtMirrorFrames
end
