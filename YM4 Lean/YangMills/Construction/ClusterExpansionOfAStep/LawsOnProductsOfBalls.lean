import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBondsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
namespace BallLaws
set_option linter.unusedSectionVars false
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ} {p : ℝ → ℝ}
def ballProduct (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_ballProduct : IsOpen (ballProduct ι ρ) := by
  have hEq : ballProduct ι ρ = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
    ext η
    simp [ballProduct]
  rw [hEq]
  exact isOpen_iInter_of_finite fun b => isOpen_lt (by fun_prop) continuous_const
theorem zero_mem_ballProduct (hρ : 0 < ρ) : (0 : BondField ι) ∈ ballProduct ι ρ := fun b => by simpa using hρ
theorem ballProduct_subset_closedBall (hρ : 0 < ρ) :
    ballProduct ι ρ ⊆ Metric.closedBall (0 : BondField ι) ρ := by
  intro η hη
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hρ.le).2 fun b => (hη b).le
theorem exists_abs_le_on_ballProduct (hρ : 0 < ρ) {f : BondField ι → ℝ} (hf : Continuous f) :
    ∃ M, ∀ η ∈ ballProduct ι ρ, |f η| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun η hη => by simpa [Real.norm_eq_abs] using hC η (ballProduct_subset_closedBall hρ hη)⟩
theorem cutoff_nonneg (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < ρ) : 0 ≤ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoff_nonneg_of_lt <;> assumption
theorem measurable_cutoffFactor_norm (hp : IsCutoff ρ p) :
    Measurable fun v : BondVector => cutoffFactor ρ p ‖v‖ := by
  classical
  have hc : ContinuousOn (fun u => Real.exp (-p u)) (Set.Ico 0 ρ) :=
    (hp.smooth.continuousOn.neg).rexp
  have hm := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const measurableSet_Ico
  have he : (fun v : BondVector => cutoffFactor ρ p ‖v‖) =
      ((Set.Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) fun _ => (0 : ℝ)) ∘ fun v => ‖v‖ := by
    funext v
    simp [cutoffFactor, Set.piecewise, norm_nonneg]
  rw [he]
  exact hm.comp measurable_norm
theorem measurable_radialWeightProd (hp : IsCutoff ρ p) :
    Measurable (radialWeightProd (ι := ι) (cutoffFactor ρ p)) := by
  unfold radialWeightProd
  exact Finset.measurable_prod _ fun b _ => (measurable_cutoffFactor_norm hp).comp (measurable_pi_apply b)
theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem radialWeightProd_nonneg (η : BondField ι) : 0 ≤ radialWeightProd (cutoffFactor ρ p) η :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _
theorem radialWeightProd_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) (η : BondField ι) :
    radialWeightProd (cutoffFactor ρ p) η ≤ 1 := by
  refine Finset.prod_le_one (fun _ _ => cutoffFactor_nonneg _) fun b _ => ?_
  unfold cutoffFactor
  split_ifs with h
  · exact Real.exp_le_one_iff.mpr (by linarith [cutoff_nonneg hρ hp (norm_nonneg (η b)) h])
  · exact zero_le_one
theorem radialWeightProd_pos {η : BondField ι} (hη : η ∈ ballProduct ι ρ) :
    0 < radialWeightProd (cutoffFactor ρ p) η := by
  refine Finset.prod_pos fun b _ => ?_
  unfold cutoffFactor
  rw [if_pos (hη b)]
  exact Real.exp_pos _
theorem radialWeightProd_eq_zero {η : BondField ι} (hη : η ∉ ballProduct ι ρ) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by
  simp only [ballProduct, Set.mem_ofPred_eq, not_forall, not_lt] at hη
  obtain ⟨b, hb⟩ := hη
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold cutoffFactor
  rw [if_neg (not_lt.mpr hb)]
def radialLaw (ι : Type) [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) : Measure (BondField ι) :=
  (volume.restrict (ballProduct ι ρ)).withDensity fun η => ENNReal.ofReal (radialWeightProd (cutoffFactor ρ p) η)
theorem isFiniteMeasure_restrict_ballProduct (hρ : 0 < ρ) :
    IsFiniteMeasure ((volume : Measure (BondField ι)).restrict (ballProduct ι ρ)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (Metric.isBounded_closedBall.subset (ballProduct_subset_closedBall hρ)).measure_lt_top
theorem isFiniteMeasure_radialLaw (hρ : 0 < ρ) (hp : IsCutoff ρ p) : IsFiniteMeasure (radialLaw ι ρ p) := by
  have := isFiniteMeasure_restrict_ballProduct (ι := ι) hρ
  refine isFiniteMeasure_withDensity_ofReal ?_
  refine (hasFiniteIntegral_const (1 : ℝ)).mono' ?_
  exact Filter.Eventually.of_forall fun η => by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialWeightProd_nonneg η)]
    exact radialWeightProd_le_one hρ hp η
theorem integral_radialLaw (hp : IsCutoff ρ p) (f : BondField ι → ℝ) :
    ∫ η, f η ∂(radialLaw ι ρ p) = ∫ η, f η * radialWeightProd (cutoffFactor ρ p) η := by
  unfold radialLaw
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((measurable_radialWeightProd hp).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [ENNReal.toReal_ofReal (radialWeightProd_nonneg η), smul_eq_mul]
    ring
  · intro η hη
    simp [radialWeightProd_eq_zero hη]
theorem radialLaw_neZero (hρ : 0 < ρ) (hp : IsCutoff ρ p) : NeZero (radialLaw ι ρ p) := by
  refine ⟨fun h => ?_⟩
  unfold radialLaw at h
  rw [withDensity_eq_zero_iff (measurable_radialWeightProd hp).ennreal_ofReal.aemeasurable] at h
  have h1 := (ae_restrict_iff' (isOpen_ballProduct (ι := ι) (ρ := ρ)).measurableSet).1 h
  rw [ae_iff] at h1
  have hsub : ballProduct ι ρ ⊆ {a | ¬(a ∈ ballProduct ι ρ →
      (fun η => ENNReal.ofReal (radialWeightProd (cutoffFactor ρ p) η)) a = (0 : BondField ι → ENNReal) a)} := by
    intro η hη hh
    have := hh hη
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    linarith [radialWeightProd_pos (p := p) hη]
  have h2 := measure_mono_null hsub h1
  exact (isOpen_ballProduct.measure_pos volume ⟨0, zero_mem_ballProduct hρ⟩).ne' h2
theorem ae_mem_ballProduct : ∀ᵐ η ∂(radialLaw ι ρ p), η ∈ ballProduct ι ρ :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem isOpen_ballProduct.measurableSet)
theorem secondDerivAlong_linComb {Ψ₀ Ψ₁ : BondField ι → ℝ} (h₀ : ContDiff ℝ 3 Ψ₀) (h₁ : ContDiff ℝ 3 Ψ₁)
    (c₀ c₁ : ℝ) (η u w : BondField ι) :
    secondDerivAlong (fun ζ => c₀ * Ψ₀ ζ + c₁ * Ψ₁ ζ) η u w =
      c₀ * secondDerivAlong Ψ₀ η u w + c₁ * secondDerivAlong Ψ₁ η u w := by
  have d₀ : Differentiable ℝ Ψ₀ := h₀.differentiable (by norm_num)
  have d₁ : Differentiable ℝ Ψ₁ := h₁.differentiable (by norm_num)
  have e₀ : Differentiable ℝ fun ζ => fderiv ℝ Ψ₀ ζ u :=
    ((h₀.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have e₁ : Differentiable ℝ fun ζ => fderiv ℝ Ψ₁ ζ u :=
    ((h₁.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
  have h : (fun ζ => fderiv ℝ (fun ζ' => c₀ * Ψ₀ ζ' + c₁ * Ψ₁ ζ') ζ u) =
      fun ζ => c₀ * fderiv ℝ Ψ₀ ζ u + c₁ * fderiv ℝ Ψ₁ ζ u := by
    funext ζ
    have := (((d₀ ζ).hasFDerivAt.const_mul c₀).add ((d₁ ζ).hasFDerivAt.const_mul c₁)).fderiv
    erw [this]
    simp
  unfold secondDerivAlong
  rw [h]
  have := (((e₀ η).hasFDerivAt.const_mul c₀).add ((e₁ η).hasFDerivAt.const_mul c₁)).fderiv
  erw [this]
  simp
theorem isUniformlyConvexDecaying_convexComb {d : ι → ι → ℝ} {Ψ₀ Ψ₁ : BondField ι → ℝ} {K₀ K₁ : ι → ι → ℝ}
    {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) (H₀ : IsUniformlyConvexDecaying ρ m κ d Ψ₀ K₀)
    (H₁ : IsUniformlyConvexDecaying ρ m κ d Ψ₁ K₁) :
    IsUniformlyConvexDecaying ρ m κ d (fun ζ => (1 - v) * Ψ₀ ζ + v * Ψ₁ ζ)
      fun b b' => (1 - v) * K₀ b b' + v * K₁ b b' := by
  have hv : 0 ≤ 1 - v := by linarith
  refine ⟨(contDiff_const.mul H₀.smooth).add (contDiff_const.mul H₁.smooth), ?_, ?_, ?_, ?_⟩
  · intro η hη u
    rw [secondDerivAlong_linComb H₀.smooth H₁.smooth]
    have a₀ := H₀.floor η hη u
    have a₁ := H₁.floor η hη u
    nlinarith [mul_le_mul_of_nonneg_left a₀ hv, mul_le_mul_of_nonneg_left a₁ h0]
  · intro η hη b b' e e'
    rw [secondDerivAlong_linComb H₀.smooth H₁.smooth]
    have a₀ := H₀.kernel η hη b b' e e'
    have a₁ := H₁.kernel η hη b b' e e'
    calc |(1 - v) * secondDerivAlong Ψ₀ η (bondVariation b e) (bondVariation b' e') +
            v * secondDerivAlong Ψ₁ η (bondVariation b e) (bondVariation b' e')|
        ≤ (1 - v) * |secondDerivAlong Ψ₀ η (bondVariation b e) (bondVariation b' e')| +
            v * |secondDerivAlong Ψ₁ η (bondVariation b e) (bondVariation b' e')| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hv, abs_of_nonneg h0]
      _ ≤ (1 - v) * (K₀ b b' * ‖e‖ * ‖e'‖) + v * (K₁ b b' * ‖e‖ * ‖e'‖) := by gcongr
      _ = ((1 - v) * K₀ b b' + v * K₁ b b') * ‖e‖ * ‖e'‖ := by ring
  · intro b b'
    simp only [H₀.symm b b', H₁.symm b b']
  · intro b
    have a₀ := H₀.standingConstraints b
    have a₁ := H₁.standingConstraints b
    have hsplit : ∑ b', ((1 - v) * K₀ b b' + v * K₁ b b') * (Real.exp (2 * κ * d b b') - 1) =
        (1 - v) * ∑ b', K₀ b b' * (Real.exp (2 * κ * d b b') - 1) +
          v * ∑ b', K₁ b b' * (Real.exp (2 * κ * d b b') - 1) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left a₀ hv, mul_le_mul_of_nonneg_left a₁ h0]
theorem secondDerivAlong_zero_left (Ψ : BondField ι → ℝ) (η w : BondField ι) :
    secondDerivAlong Ψ η 0 w = 0 := by
  unfold secondDerivAlong
  simp
theorem secondDerivAlong_zero_right (Ψ : BondField ι → ℝ) (η u : BondField ι) :
    secondDerivAlong Ψ η u 0 = 0 := by
  unfold secondDerivAlong
  simp
theorem differentiable_fderiv_apply {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (u : BondField ι) :
    Differentiable ℝ fun ζ => fderiv ℝ Ψ ζ u :=
  ((h.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)
theorem fderiv_comp_clm {ι₀ : Type} [Fintype ι₀] {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ)
    (T : BondField ι₀ →L[ℝ] BondField ι) (ζ u : BondField ι₀) :
    fderiv ℝ (fun η => Ψ (T η)) ζ u = fderiv ℝ Ψ (T ζ) (T u) := by
  have d : Differentiable ℝ Ψ := h.differentiable (by norm_num)
  have := ((d (T ζ)).hasFDerivAt.comp ζ T.hasFDerivAt).fderiv
  erw [this]
  rfl
theorem secondDerivAlong_comp_clm {ι₀ : Type} [Fintype ι₀] {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ)
    (T : BondField ι₀ →L[ℝ] BondField ι) (η u w : BondField ι₀) :
    secondDerivAlong (fun ζ => Ψ (T ζ)) η u w = secondDerivAlong Ψ (T η) (T u) (T w) := by
  unfold secondDerivAlong
  have e : (fun ζ => fderiv ℝ (fun ζ' => Ψ (T ζ')) ζ u) = fun ζ => fderiv ℝ Ψ (T ζ) (T u) := by
    funext ζ
    exact fderiv_comp_clm h T ζ u
  rw [e]
  have := ((differentiable_fderiv_apply h (T u) (T η)).hasFDerivAt.comp η T.hasFDerivAt).fderiv
  erw [this]
  rfl
theorem secondDerivAlong_add {f g : BondField ι → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (η u w : BondField ι) :
    secondDerivAlong (fun ζ => f ζ + g ζ) η u w = secondDerivAlong f η u w + secondDerivAlong g η u w := by
  have df : Differentiable ℝ f := hf.differentiable (by norm_num)
  have dg : Differentiable ℝ g := hg.differentiable (by norm_num)
  unfold secondDerivAlong
  have e : (fun ζ => fderiv ℝ (fun ζ' => f ζ' + g ζ') ζ u) = fun ζ => fderiv ℝ f ζ u + fderiv ℝ g ζ u := by
    funext ζ
    have := ((df ζ).hasFDerivAt.add (dg ζ).hasFDerivAt).fderiv
    erw [this]
    rfl
  rw [e]
  have := ((differentiable_fderiv_apply hf u η).hasFDerivAt.add
    (differentiable_fderiv_apply hg u η).hasFDerivAt).fderiv
  erw [this]
  rfl
theorem kernel_nonneg {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} (hρ : 0 < ρ)
    (H : IsUniformlyConvexDecaying ρ m κ d Ψ K) (b b' : ι) : 0 ≤ K b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.kernel_nonneg <;> assumption
theorem pseudoMetric_nonneg {d : ι → ι → ℝ} (hd : IsPseudoMetricOnBonds d) (b b' : ι) : 0 ≤ d b b' := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.pseudoMetric_nonneg <;> assumption
end BallLaws
open ColdStepAtMirrorFrames
def extendByZero {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι] (j : ι₀ → ι) : BondField ι₀ →L[ℝ] BondField ι :=
  ∑ a, (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) (j a)).comp
    (ContinuousLinearMap.proj a : BondField ι₀ →L[ℝ] BondVector)
theorem extendByZero_apply {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι] (j : ι₀ → ι) (ξ : BondField ι₀) (b : ι) :
    extendByZero j ξ b = ∑ a, (Pi.single (j a) (ξ a) : BondField ι) b := by
  simp [extendByZero, ContinuousLinearMap.sum_apply, Finset.sum_apply]
theorem extendByZero_apply_image {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι] {j : ι₀ → ι}
    (hj : Function.Injective j) (ξ : BondField ι₀) (a : ι₀) : extendByZero j ξ (j a) = ξ a := by
  rw [extendByZero_apply, Finset.sum_eq_single a]
  · simp
  · intro a' _ h
    exact Pi.single_eq_of_ne (fun e => h (hj e).symm) _
  · intro h
    exact absurd (Finset.mem_univ a) h
theorem extendByZero_apply_of_not_mem_range {ι ι₀ : Type} [Fintype ι₀] [DecidableEq ι] {j : ι₀ → ι}
    (ξ : BondField ι₀) {b : ι} (hb : ∀ a, j a ≠ b) : extendByZero j ξ b = 0 := by
  rw [extendByZero_apply]
  exact Finset.sum_eq_zero fun a _ => Pi.single_eq_of_ne (fun e => hb a e.symm) _
def restrictToSet {ι : Type} [DecidableEq ι] (X : Finset ι) (η : BondField ι) : BondField ι :=
  fun b => if b ∈ X then η b else 0
def restrictedPotential {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℝ) (X : Finset ι) (Ψ : BondField ι → ℝ)
    (η : BondField ι) : ℝ :=
  Ψ (restrictToSet X η) + c / 2 * ∑ b ∈ Finset.univ \ X, ‖η b‖ ^ 2
def restrictedGradBound {ι : Type} [Fintype ι] [DecidableEq ι] (ρ c C₁ : ℝ) (X : Finset ι) (K : ι → ι → ℝ)
    (b : ι) : ℝ :=
  if b ∈ X then ρ * ∑ b' ∈ Finset.univ \ X, K b b' else C₁ + c * ρ
namespace BallLaws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ m κ : ℝ}
def restrictCLM (X : Finset ι) : BondField ι →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => if b ∈ X then ContinuousLinearMap.proj b else 0
theorem restrictCLM_apply (X : Finset ι) (η : BondField ι) : restrictCLM X η = restrictToSet X η := by
  funext b
  by_cases h : b ∈ X <;> simp [restrictCLM, restrictToSet, h]
theorem restrictCLM_bondVariation (X : Finset ι) (b : ι) (e : BondVector) :
    restrictCLM X (bondVariation b e) = if b ∈ X then bondVariation b e else 0 := by
  funext x
  rw [restrictCLM_apply]
  unfold restrictToSet bondVariation
  by_cases hx : x = b
  · subst hx
    by_cases h : x ∈ X <;> simp [h]
  · by_cases h : x ∈ X <;> by_cases h' : b ∈ X <;> simp [h, h', hx]
def gaussianOn (c : ℝ) (S : Finset ι) (η : BondField ι) : ℝ := c / 2 * ∑ b ∈ S, ‖η b‖ ^ 2
theorem gaussianOn_contDiff (c : ℝ) (S : Finset ι) : ContDiff ℝ 3 (gaussianOn (ι := ι) c S) := by
  unfold gaussianOn
  refine contDiff_const.mul (ContDiff.sum fun b _ => ?_)
  exact (contDiff_apply ℝ BondVector b).norm_sq ℝ
theorem gaussianOn_hasFDerivAt (c : ℝ) (S : Finset ι) (η : BondField ι) :
    HasFDerivAt (gaussianOn c S)
      ((c / 2) • ∑ b ∈ S, (2 : ℕ) • (innerSL ℝ (η b)).comp
        (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector)) η := by
  unfold gaussianOn
  have := (HasFDerivAt.fun_sum (u := S) (A := fun b (ζ : BondField ι) => ‖ζ b‖ ^ 2) (x := η)
    (fun b _ => (hasFDerivAt_apply (𝕜 := ℝ) b η).norm_sq)).const_mul (c / 2)
  exact this
theorem gaussianOn_fderiv (c : ℝ) (S : Finset ι) (η u : BondField ι) :
    fderiv ℝ (gaussianOn c S) η u = c * ∑ b ∈ S, inner ℝ (η b) (u b) := by
  rw [(gaussianOn_hasFDerivAt c S η).fderiv]
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Nat.cast_ofNat]
  ring
theorem gaussianOn_secondDerivAlong (c : ℝ) (S : Finset ι) (η u w : BondField ι) :
    secondDerivAlong (gaussianOn c S) η u w = c * ∑ b ∈ S, inner ℝ (w b) (u b) := by
  unfold secondDerivAlong
  have e : (fun ζ => fderiv ℝ (gaussianOn c S) ζ u) =
      ((c • ∑ b ∈ S, ((innerSL ℝ (u b)).comp
        (ContinuousLinearMap.proj b : BondField ι →L[ℝ] BondVector)) :
        BondField ι →L[ℝ] ℝ) : BondField ι → ℝ) := by
    funext ζ
    rw [gaussianOn_fderiv]
    simp only [smul_apply, sum_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
  rw [e, ContinuousLinearMap.fderiv]
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => real_inner_comm _ _
theorem restrictedPotential_eq (c : ℝ) (X : Finset ι) (Ψ : BondField ι → ℝ) :
    restrictedPotential c X Ψ = fun η => Ψ (restrictCLM X η) + gaussianOn c (Finset.univ \ X) η := by
  funext η
  simp [restrictedPotential, gaussianOn, restrictCLM_apply]
theorem restrictCLM_mem {X : Finset ι} {η : BondField ι} (hρ : 0 < ρ) (hη : ∀ b, ‖η b‖ < ρ) :
    ∀ b, ‖restrictCLM X η b‖ < ρ := by
  intro b
  rw [restrictCLM_apply]
  unfold restrictToSet
  split_ifs
  · exact hη b
  · simpa using hρ
theorem abs_sum_inner_bondVariation_le (S : Finset ι) (b b' : ι) (e e' : BondVector) :
    |∑ x ∈ S, inner ℝ ((bondVariation b' e' : BondField ι) x) ((bondVariation b e : BondField ι) x)| ≤
      (if b = b' then 1 else 0) * ‖e‖ * ‖e'‖ := by
  by_cases h : b = b'
  · subst h
    rw [if_pos rfl, one_mul]
    by_cases hb : b ∈ S
    · rw [Finset.sum_eq_single b]
      · simp only [bondVariation, Pi.single_eq_same]
        refine (abs_real_inner_le_norm _ _).trans (by rw [mul_comm])
      · intro x _ hx
        simp [bondVariation, Pi.single_eq_of_ne hx]
      · exact fun hn => absurd hb hn
    · rw [Finset.sum_eq_zero]
      · simp only [abs_zero]; positivity
      · intro x hx
        have hne : x ≠ b := fun hh => hb (hh ▸ hx)
        simp [bondVariation, Pi.single_eq_of_ne hne]
  · rw [if_neg h, Finset.sum_eq_zero]
    · simp
    · intro x _
      by_cases hx : x = b
      · subst hx
        have hne : x ≠ b' := h
        simp [bondVariation, Pi.single_eq_of_ne hne]
      · simp [bondVariation, Pi.single_eq_of_ne hx]
theorem isUniformlyConvexDecaying_restrictedPotential {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    {c : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hd : IsPseudoMetricOnBonds d) (H : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hc : 2 * m ≤ c) (X : Finset ι) :
    IsUniformlyConvexDecaying ρ m κ d (restrictedPotential c X Ψ) fun b b' => K b b' + (if b = b' then c else 0) := by
  have hc0 : 0 ≤ c := by linarith
  have s1 : ContDiff ℝ 3 fun η => Ψ (restrictCLM X η) := H.smooth.comp (restrictCLM X).contDiff
  have s2 := gaussianOn_contDiff (ι := ι) c (Finset.univ \ X)
  have sec : ∀ η u w, secondDerivAlong (restrictedPotential c X Ψ) η u w =
      secondDerivAlong Ψ (restrictCLM X η) (restrictCLM X u) (restrictCLM X w) +
        c * ∑ x ∈ Finset.univ \ X, inner ℝ (w x) (u x) := by
    intro η u w
    rw [restrictedPotential_eq, secondDerivAlong_add s1 s2, secondDerivAlong_comp_clm H.smooth,
      gaussianOn_secondDerivAlong]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [restrictedPotential_eq]
    exact s1.add s2
  · intro η hη u
    rw [sec]
    have a := H.floor (restrictCLM X η) (restrictCLM_mem hρ hη) (restrictCLM X u)
    have e1 : ∑ b, ‖u b‖ ^ 2 = ∑ b, ‖restrictCLM X u b‖ ^ 2 + ∑ x ∈ Finset.univ \ X, ‖u x‖ ^ 2 := by
      rw [← Finset.sum_sdiff (Finset.subset_univ X), add_comm]
      congr 1
      · have hin : ∑ b, ‖restrictCLM X u b‖ ^ 2 = ∑ b ∈ X, ‖u b‖ ^ 2 := by
          rw [← Finset.sum_sdiff (Finset.subset_univ X)]
          have z : ∑ b ∈ Finset.univ \ X, ‖restrictCLM X u b‖ ^ 2 = 0 := by
            refine Finset.sum_eq_zero fun b hb => ?_
            have hb' : b ∉ X := (Finset.mem_sdiff.mp hb).2
            simp [restrictCLM_apply, restrictToSet, hb']
          rw [z, zero_add]
          refine Finset.sum_congr rfl fun b hb => ?_
          simp [restrictCLM_apply, restrictToSet, hb]
        exact hin.symm
    have e2 : ∑ x ∈ Finset.univ \ X, inner ℝ (u x) (u x) = ∑ x ∈ Finset.univ \ X, ‖u x‖ ^ 2 :=
      Finset.sum_congr rfl fun x _ => real_inner_self_eq_norm_sq _
    rw [e1, e2]
    have hS : 0 ≤ ∑ x ∈ Finset.univ \ X, ‖u x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    nlinarith
  · intro η hη b b' e e'
    rw [sec]
    have hK := kernel_nonneg hρ H b b'
    have a1 : |secondDerivAlong Ψ (restrictCLM X η) (restrictCLM X (bondVariation b e))
        (restrictCLM X (bondVariation b' e'))| ≤ K b b' * ‖e‖ * ‖e'‖ := by
      rw [restrictCLM_bondVariation, restrictCLM_bondVariation]
      by_cases h1 : b ∈ X
      · by_cases h2 : b' ∈ X
        · rw [if_pos h1, if_pos h2]
          exact H.kernel (restrictCLM X η) (restrictCLM_mem hρ hη) b b' e e'
        · rw [if_neg h2, secondDerivAlong_zero_right, abs_zero]
          positivity
      · rw [if_neg h1, secondDerivAlong_zero_left, abs_zero]
        positivity
    have a2 := abs_sum_inner_bondVariation_le (Finset.univ \ X) b b' e e'
    calc _ ≤ |secondDerivAlong Ψ (restrictCLM X η) (restrictCLM X (bondVariation b e))
            (restrictCLM X (bondVariation b' e'))| +
          |c * ∑ x ∈ Finset.univ \ X,
            inner ℝ ((bondVariation b' e' : BondField ι) x) ((bondVariation b e : BondField ι) x)| :=
          abs_add_le _ _
      _ ≤ K b b' * ‖e‖ * ‖e'‖ + c * ((if b = b' then 1 else 0) * ‖e‖ * ‖e'‖) := by
          rw [abs_mul, abs_of_nonneg hc0]
          gcongr
      _ = (K b b' + if b = b' then c else 0) * ‖e‖ * ‖e'‖ := by
          by_cases h : b = b' <;> simp [h]; ring
  · intro b b'
    simp only [H.symm b b', eq_comm]
  · intro b
    have hrow := H.standingConstraints b
    have e : ∑ b', (K b b' + if b = b' then c else 0) * (Real.exp (2 * κ * d b b') - 1) =
        ∑ b', K b b' * (Real.exp (2 * κ * d b b') - 1) := by
      refine Finset.sum_congr rfl fun b' _ => ?_
      by_cases h : b = b'
      · subst h
        simp [hd.self]
      · simp [h]
    rw [e]
    exact hrow
theorem bondGradNorm_le_of_forall {f : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ e : BondVector, |fderiv ℝ f η (bondVariation b e)| ≤ B * ‖e‖) : bondGradNorm f b η ≤ B := by
  unfold bondGradNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun e => ?_
  simpa [bondVariation, Real.norm_eq_abs] using h e
theorem abs_fderiv_bondVariation_le (f : BondField ι → ℝ) (η : BondField ι) (b : ι) (e : BondVector) :
    |fderiv ℝ f η (bondVariation b e)| ≤ bondGradNorm f b η * ‖e‖ := by
  unfold bondGradNorm
  have := ((fderiv ℝ f η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm e
  simpa [bondVariation, Real.norm_eq_abs] using this
theorem fderiv_restrictedPotential {Ψ : BondField ι → ℝ} (h : ContDiff ℝ 3 Ψ) (c : ℝ) (X : Finset ι)
    (η a : BondField ι) :
    fderiv ℝ (restrictedPotential c X Ψ) η a = fderiv ℝ Ψ (restrictCLM X η) (restrictCLM X a) +
      c * ∑ x ∈ Finset.univ \ X, inner ℝ (η x) (a x) := by
  have d₁ : DifferentiableAt ℝ (fun ζ => Ψ (restrictCLM X ζ)) η :=
    (h.comp (restrictCLM X).contDiff).differentiable (by norm_num) η
  have d₂ : DifferentiableAt ℝ (gaussianOn c (Finset.univ \ X)) η :=
    (gaussianOn_contDiff c _).differentiable (by norm_num) η
  rw [restrictedPotential_eq]
  have := (d₁.hasFDerivAt.add d₂.hasFDerivAt).fderiv
  erw [this]
  simp only [add_apply]
  rw [fderiv_comp_clm h, gaussianOn_fderiv]
end BallLaws
end YangMills.Construction.ClusterExpansionOfAStep
end
