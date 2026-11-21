import YangMills.Construction.ClusterExpansionOfAStep.CovarianceInSupNorms
import YangMills.Construction.ClusterExpansionOfAStep.CovarianceOfAFunctionOfSomeBonds
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ConvexMeasures
open YangMills.Construction.ColdStepAtMirrorFrames
namespace LocalCovariance
section Cutoff
variable {J : Type} [Fintype J] {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem radialWeightProd_nonneg (z : BondField J) : 0 ≤ radialWeightProd (cutoffFactor ρ p) z :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _
theorem continuous_radialWeightProd (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)) :
    Continuous (radialWeightProd (ι := J) (cutoffFactor ρ p)) := by
  have e : radialWeightProd (ι := J) (cutoffFactor ρ p) =
      fun z => ∏ b, (fun u => cutoffFactor ρ p (max u 0)) ‖z b‖ := by
    funext z
    unfold radialWeightProd
    exact Finset.prod_congr rfl fun b _ => by simp
  rw [e]
  exact continuous_finsetProd _ fun b _ => hr.smooth.continuous.comp (continuous_apply b).norm
theorem lt_of_cutoffFactor_ne_zero {u : ℝ} (h : cutoffFactor ρ p u ≠ 0) : u < ρ := by
  by_contra hc
  exact h (by simp [cutoffFactor, not_lt.mp hc])
theorem norm_lt_of_radialWeightProd_ne_zero {z : BondField J}
    (h : radialWeightProd (cutoffFactor ρ p) z ≠ 0) (b : J) : ‖z b‖ < ρ := by
  apply lt_of_cutoffFactor_ne_zero (p := p)
  intro h0
  exact h (Finset.prod_eq_zero (Finset.mem_univ b) h0)
theorem radialWeightProd_pos {z : BondField J} (hz : ∀ b, ‖z b‖ < ρ) :
    0 < radialWeightProd (cutoffFactor ρ p) z :=
  Finset.prod_pos fun b _ => by simp [cutoffFactor, hz b, Real.exp_pos]
theorem hasCompactSupport_radialWeightProd (hρ : 0 < ρ) :
    HasCompactSupport (radialWeightProd (ι := J) (cutoffFactor ρ p)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : BondField J) ρ) fun z hz => ?_
  by_contra hne
  apply hz
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (norm_lt_of_radialWeightProd_ne_zero hne b).le
theorem ballDensity_nonneg (Ψ : BondField J → ℝ) (z : BondField J) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ z :=
  mul_nonneg (radialWeightProd_nonneg z) (Real.exp_pos _).le
theorem continuous_ballDensity (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    {Ψ : BondField J → ℝ} (hΨ : Continuous Ψ) :
    Continuous (ballDensity (cutoffFactor ρ p) Ψ) :=
  (continuous_radialWeightProd hr).mul (Real.continuous_exp.comp hΨ.neg)
theorem hasCompactSupport_ballDensity (hρ : 0 < ρ) (Ψ : BondField J → ℝ) :
    HasCompactSupport (ballDensity (cutoffFactor ρ p) Ψ) :=
  HasCompactSupport.mul_right (f' := fun z => Real.exp (-Ψ z)) (hasCompactSupport_radialWeightProd hρ)
theorem norm_lt_of_ballDensity_ne_zero {Ψ : BondField J → ℝ} {z : BondField J}
    (h : ballDensity (cutoffFactor ρ p) Ψ z ≠ 0) (b : J) : ‖z b‖ < ρ := by
  apply norm_lt_of_radialWeightProd_ne_zero (p := p)
  intro h0
  exact h (by simp [ballDensity, h0])
theorem integrable_mul_ballDensity (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    {Ψ h : BondField J → ℝ} (hΨ : Continuous Ψ) (hh : Continuous h) :
    Integrable fun z => h z * ballDensity (cutoffFactor ρ p) Ψ z :=
  Continuous.integrable_of_hasCompactSupport (hh.mul (continuous_ballDensity hr hΨ))
    (hasCompactSupport_ballDensity hρ Ψ).mul_left
theorem integral_ballDensity_pos (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    {Ψ : BondField J → ℝ} (hΨ : Continuous Ψ) :
    0 < ∫ z, ballDensity (cutoffFactor ρ p) Ψ z := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (continuous_ballDensity hr hΨ) (hasCompactSupport_ballDensity hρ Ψ)
    (fun z => ballDensity_nonneg Ψ z) ?_
  have h0 : ∀ b, ‖(0 : BondField J) b‖ < ρ := fun b => by simpa using hρ
  exact (mul_pos (radialWeightProd_pos h0) (Real.exp_pos _)).ne'
theorem abs_ballExpectation_le (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    {Ψ h : BondField J → ℝ} {β : ℝ} (hΨ : Continuous Ψ) (hh : Continuous h)
    (hb : ∀ z : BondField J, (∀ b, ‖z b‖ < ρ) → |h z| ≤ β) :
    |ballExpectation (cutoffFactor ρ p) Ψ h| ≤ β := by
  have hZ := integral_ballDensity_pos (p := p) hρ hr hΨ
  have hi : Integrable (ballDensity (cutoffFactor ρ p) Ψ) :=
    (continuous_ballDensity hr hΨ).integrable_of_hasCompactSupport (hasCompactSupport_ballDensity hρ Ψ)
  have h1 : ‖∫ z, h z * ballDensity (cutoffFactor ρ p) Ψ z‖ ≤
      ∫ z, β * ballDensity (cutoffFactor ρ p) Ψ z := by
    apply norm_integral_le_of_norm_le (hi.const_mul β)
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases h0 : ballDensity (cutoffFactor ρ p) Ψ z = 0
    · simp [h0]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (ballDensity_nonneg Ψ z)]
      exact mul_le_mul_of_nonneg_right (hb z (norm_lt_of_ballDensity_ne_zero h0)) (ballDensity_nonneg Ψ z)
  rw [integral_const_mul, Real.norm_eq_abs] at h1
  unfold ballExpectation
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact h1
theorem hasDerivAt_integral_mul_weight {q q' : ℝ → BondField J → ℝ} {w : BondField J → ℝ}
    (hq : Continuous (Function.uncurry q)) (hq' : Continuous (Function.uncurry q'))
    (hd : ∀ t z, HasDerivAt (fun s => q s z) (q' t z) t) (hw : Continuous w)
    (hc : HasCompactSupport w) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z, q t z * w z) (∫ z, q' t₀ z * w z) t₀ := by
  have hK : IsCompact (Metric.closedBall t₀ 1 ×ˢ tsupport w) :=
    (isCompact_closedBall t₀ 1).prod hc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hq'.continuousOn
  have hcw : ∀ t, Continuous (q t) := fun t => hq.comp (Continuous.prodMk_right t)
  have hcw' : ∀ t, Continuous (q' t) := fun t => hq'.comp (Continuous.prodMk_right t)
  have hb : Integrable fun z => M * |w z| :=
    (Continuous.integrable_of_hasCompactSupport hw.abs hc.abs).const_mul M
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball t₀ 1)
    (F := fun t z => q t z * w z) (F' := fun t z => q' t z * w z)
    (bound := fun z => M * |w z|) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => ((hcw t).mul hw).aestronglyMeasurable)
    (Continuous.integrable_of_hasCompactSupport ((hcw t₀).mul hw) hc.mul_left)
    ((hcw' t₀).mul hw).aestronglyMeasurable ?_ hb ?_).2
  · refine Filter.Eventually.of_forall fun z t ht => ?_
    by_cases hz : z ∈ tsupport w
    · rw [norm_mul, Real.norm_eq_abs (w z)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact hM (t, z) ⟨Metric.ball_subset_closedBall ht, hz⟩
    · have h0 : w z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [h0]
  · exact Filter.Eventually.of_forall fun z t _ => (hd t z).mul_const (w z)
end Cutoff
section Block
variable {ι : Type} [Fintype ι] [DecidableEq ι] (X : Finset ι)
abbrev Complement : Type := {b : ι // b ∉ X}
def extendByZero : BondField (Complement X) →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b =>
    if h : b ∉ X then ContinuousLinearMap.proj (⟨b, h⟩ : Complement X) else 0
theorem extendByZero_apply_compl (z : BondField (Complement X)) (b : Complement X) :
    extendByZero X z b = z b := by
  have h : ((extendByZero X z : BondField ι) (b : ι)) =
      (if h : (b : ι) ∉ X then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Complement X => BondVector)
        (⟨b, h⟩ : Complement X) else 0) z := rfl
  rw [h, dif_pos b.2]
  rfl
theorem extendByZero_apply_mem {b : ι} (hb : b ∈ X) (z : BondField (Complement X)) :
    extendByZero X z b = 0 := by
  have h : ((extendByZero X z : BondField ι) b) =
      (if h : b ∉ X then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Complement X => BondVector)
        (⟨b, h⟩ : Complement X) else 0) z := rfl
  rw [h, dif_neg (not_not.mpr hb)]
  rfl
theorem extendByZero_single (b : Complement X) (e : BondVector) :
    extendByZero X (Pi.single b e) = (Pi.single (b : ι) e : BondField ι) := by
  funext c
  by_cases hc : c ∈ X
  · rw [extendByZero_apply_mem X hc, Pi.single_eq_of_ne]
    rintro rfl
    exact b.2 hc
  · have e1 := extendByZero_apply_compl X (Pi.single b e) ⟨c, hc⟩
    simp only at e1
    rw [e1]
    by_cases hb : (⟨c, hc⟩ : Complement X) = b
    · subst hb
      simp
    · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne]
      intro h
      exact hb (Subtype.ext h)
theorem sum_complement (f : ι → ℝ) : ∑ b : Complement X, f b = ∑ b ∈ Xᶜ, f b :=
  (Finset.sum_subtype Xᶜ (p := fun b => b ∉ X) (by simp) f).symm
theorem prod_complement (f : ι → ℝ) : ∏ b : Complement X, f b = ∏ b ∈ Xᶜ, f b :=
  (Finset.prod_subtype Xᶜ (p := fun b => b ∉ X) (by simp) f).symm
theorem sum_complement_le {f : ι → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑ b : Complement X, f b ≤ ∑ b, f b := by
  rw [sum_complement]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hf b
variable {X} {ρ : ℝ} {p : ℝ → ℝ}
structure SupportedInBalls (X : Finset ι) (ρ : ℝ) (ξ : BondField ι) : Prop where
  vanishes : ∀ b, b ∉ X → ξ b = 0
  norm_lt : ∀ b, b ∈ X → ‖ξ b‖ < ρ
theorem shift_apply_compl {ξ : BondField ι} (h0 : ∀ b, b ∉ X → ξ b = 0)
    (z : BondField (Complement X)) (b : Complement X) : (ξ + extendByZero X z) b = z b := by
  simp [extendByZero_apply_compl, h0 b b.2]
theorem shift_apply_mem (ξ : BondField ι) (z : BondField (Complement X)) {b : ι} (hb : b ∈ X) :
    (ξ + extendByZero X z) b = ξ b := by
  simp [extendByZero_apply_mem X hb]
theorem shift_norm_lt {ξ : BondField ι} (hξ : SupportedInBalls X ρ ξ) {z : BondField (Complement X)}
    (hz : ∀ b, ‖z b‖ < ρ) (b : ι) : ‖(ξ + extendByZero X z) b‖ < ρ := by
  by_cases hb : b ∈ X
  · rw [shift_apply_mem ξ z hb]
    exact hξ.norm_lt b hb
  · have := shift_apply_compl hξ.vanishes z ⟨b, hb⟩
    simp only at this
    rw [this]
    exact hz _
def blockWeight (X : Finset ι) (ρ : ℝ) (p : ℝ → ℝ) (ξ : BondField ι) : ℝ :=
  ∏ b ∈ X, cutoffFactor ρ p ‖ξ b‖
theorem blockWeight_nonneg (ξ : BondField ι) : 0 ≤ blockWeight X ρ p ξ :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _
theorem ballDensity_shift {ξ : BondField ι} (h0 : ∀ b, b ∉ X → ξ b = 0) (Ψ : BondField ι → ℝ)
    (z : BondField (Complement X)) :
    ballDensity (cutoffFactor ρ p) Ψ (ξ + extendByZero X z) =
      blockWeight X ρ p ξ * ballDensity (cutoffFactor ρ p) (fun z => Ψ (ξ + extendByZero X z)) z := by
  unfold ballDensity radialWeightProd blockWeight
  rw [← Finset.prod_mul_prod_compl X, mul_assoc]
  congr 1
  · exact Finset.prod_congr rfl fun b hb => by rw [shift_apply_mem ξ z hb]
  · congr 1
    rw [← prod_complement X (fun b => cutoffFactor ρ p ‖(ξ + extendByZero X z) b‖)]
    exact Finset.prod_congr rfl fun b _ => by rw [shift_apply_compl h0 z b]
theorem fderiv_comp_shift {Φ : BondField ι → ℝ} (hΦ : Differentiable ℝ Φ) (ξ : BondField ι)
    (z : BondField (Complement X)) :
    fderiv ℝ (fun z => Φ (ξ + extendByZero X z)) z =
      (fderiv ℝ Φ (ξ + extendByZero X z)).comp (extendByZero X) := by
  have h : HasFDerivAt (fun z => ξ + extendByZero X z) (extendByZero X) z :=
    (extendByZero X).hasFDerivAt.const_add ξ
  exact ((hΦ _).hasFDerivAt.comp z h).fderiv
theorem differentiable_fderiv_apply {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (u : BondField ι) :
    Differentiable ℝ fun ζ => fderiv ℝ Ψ ζ u := by
  have h2 : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  exact fun ζ => ((h2 ζ).hasFDerivAt.clm_apply (hasFDerivAt_const u ζ)).differentiableAt
theorem secondDerivAlong_comp_shift {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ) (ξ : BondField ι)
    (z u v : BondField (Complement X)) :
    secondDerivAlong (fun z => Ψ (ξ + extendByZero X z)) z u v =
      secondDerivAlong Ψ (ξ + extendByZero X z) (extendByZero X u) (extendByZero X v) := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  unfold secondDerivAlong
  have e : (fun ζ => fderiv ℝ (fun z => Ψ (ξ + extendByZero X z)) ζ u) =
      fun ζ => (fun y => fderiv ℝ Ψ y (extendByZero X u)) (ξ + extendByZero X ζ) := by
    funext ζ
    rw [fderiv_comp_shift hd]
    rfl
  rw [e, fderiv_comp_shift (differentiable_fderiv_apply hΨ _)]
  rfl
theorem secondDerivAlong_eq_fderiv_fderiv {Ψ : BondField ι → ℝ} (hΨ : ContDiff ℝ 3 Ψ)
    (ζ u v : BondField ι) :
    secondDerivAlong Ψ ζ u v = fderiv ℝ (fderiv ℝ Ψ) ζ v u := by
  have h2 : Differentiable ℝ (fderiv ℝ Ψ) :=
    (hΨ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have h : fderiv ℝ (fun y => fderiv ℝ Ψ y u) ζ = _ :=
    ((h2 ζ).hasFDerivAt.clm_apply (hasFDerivAt_const u ζ)).fderiv
  unfold secondDerivAlong
  rw [h]
  simp
theorem kernel_nonneg {m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K) (b b' : ι) : 0 ≤ K b b' := by
  have h0 : ∀ c, ‖(0 : BondField ι) c‖ < ρ := fun c => by simpa using hρ
  have e : ‖(EuclideanSpace.single 0 1 : BondVector)‖ = 1 := by simp
  have := hC.kernel 0 h0 b b' (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  rw [e, mul_one, mul_one] at this
  exact (abs_nonneg _).trans this
theorem pseudoMetric_nonneg {d : ι → ι → ℝ} (hd : IsPseudoMetricOnBonds d) (b b' : ι) :
    0 ≤ d b b' := by
  have h1 := hd.triangle b b' b
  rw [hd.self, hd.symm b' b] at h1
  linarith
theorem restrict_complement {m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ}
    (hρ : 0 < ρ) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d)
    (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K) {ξ : BondField ι} (hξ : SupportedInBalls X ρ ξ) :
    IsUniformlyConvexDecaying ρ m κ (fun b b' : Complement X => d b b')
      (fun z => Ψ (ξ + extendByZero X z)) (fun b b' : Complement X => K b b') where
  smooth := hC.smooth.comp (contDiff_const.add (extendByZero X).contDiff)
  floor := by
    intro z hz u
    rw [secondDerivAlong_comp_shift hC.smooth]
    have h := hC.floor (ξ + extendByZero X z) (shift_norm_lt hξ hz) (extendByZero X u)
    have e : ∑ b, ‖extendByZero X u b‖ ^ 2 = ∑ b : Complement X, ‖u b‖ ^ 2 := by
      rw [← Finset.sum_add_sum_compl X, ← sum_complement X (fun b => ‖extendByZero X u b‖ ^ 2),
        Finset.sum_eq_zero (s := X), zero_add]
      · exact Finset.sum_congr rfl fun b _ => by rw [extendByZero_apply_compl]
      · intro b hb
        simp [extendByZero_apply_mem X hb]
    rwa [e] at h
  kernel := by
    intro z hz b b' e e'
    rw [secondDerivAlong_comp_shift hC.smooth]
    unfold bondVariation
    rw [extendByZero_single, extendByZero_single]
    exact hC.kernel (ξ + extendByZero X z) (shift_norm_lt hξ hz) b b' e e'
  symm := fun b b' => hC.symm b b'
  standingConstraints := by
    intro b
    refine (sum_complement_le X (f := fun b' => K b b' * (Real.exp (2 * κ * d b b') - 1))
      fun b' => ?_).trans (hC.standingConstraints b)
    apply mul_nonneg (kernel_nonneg hρ hC _ _)
    have : 0 ≤ 2 * κ * d b b' := mul_nonneg (by positivity) (pseudoMetric_nonneg hd _ _)
    linarith [Real.add_one_le_exp (2 * κ * d b b')]
theorem eq_sum_bondVariation {V : BondField ι} (hV0 : ∀ b, b ∉ X → V b = 0) :
    V = ∑ b ∈ X, bondVariation b (V b) := by
  funext c
  rw [Finset.sum_apply]
  by_cases hc : c ∈ X
  · rw [Finset.sum_eq_single c]
    · simp [bondVariation]
    · intro b _ hb
      simp [bondVariation, Pi.single_eq_of_ne hb.symm]
    · exact fun h => absurd hc h
  · rw [hV0 c hc, Finset.sum_eq_zero]
    intro b hb
    have : c ≠ b := fun h => hc (h ▸ hb)
    simp [bondVariation, Pi.single_eq_of_ne this]
theorem bondGradNorm_directional_le {m κ : ℝ} {d : ι → ι → ℝ} {Ψ : BondField ι → ℝ}
    {K : ι → ι → ℝ} (hρ : 0 < ρ) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    {ξ V : BondField ι} (hξ : SupportedInBalls X ρ ξ)
    (hV0 : ∀ b, b ∉ X → V b = 0) (hV : ∀ b, ‖V b‖ ≤ 2 * ρ) (z : BondField (Complement X))
    (hz : ∀ b, ‖z b‖ < ρ) (b'' : Complement X) :
    bondGradNorm (fun z => fderiv ℝ Ψ (ξ + extendByZero X z) V) b'' z ≤
      ∑ b ∈ X, K b'' b * (2 * ρ) := by
  set ζ := ξ + extendByZero X z with hζ
  have hζb := shift_norm_lt hξ hz
  have e := fderiv_comp_shift (X := X) (differentiable_fderiv_apply hC.smooth V) ξ z
  beta_reduce at e
  unfold bondGradNorm
  rw [e]
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun b _ => mul_nonneg (kernel_nonneg hρ hC _ _) (by positivity))
  intro v
  have e1 : (((fderiv ℝ (fun y => fderiv ℝ Ψ y V) ζ).comp (extendByZero X)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Complement X => BondVector) b'')) v =
      secondDerivAlong Ψ ζ V (bondVariation (b'' : ι) v) := by
    have e2 : extendByZero X ((ContinuousLinearMap.single ℝ (fun _ : Complement X => BondVector) b'') v) =
        bondVariation (b'' : ι) v := extendByZero_single X b'' v
    simp only [ContinuousLinearMap.comp_apply, e2]
    rfl
  rw [e1, secondDerivAlong_eq_fderiv_fderiv hC.smooth]
  conv_lhs => rw [eq_sum_bondVariation hV0]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have e3 : fderiv ℝ (fderiv ℝ Ψ) ζ (bondVariation (b'' : ι) v) (bondVariation b (V b)) =
      secondDerivAlong Ψ ζ (bondVariation b (V b)) (bondVariation (b'' : ι) v) :=
    (secondDerivAlong_eq_fderiv_fderiv hC.smooth _ _ _).symm
  rw [e3, Real.norm_eq_abs]
  refine (hC.kernel ζ hζb b b'' (V b) v).trans ?_
  rw [hC.symm b b'', mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (kernel_nonneg hρ hC _ _)
  exact mul_le_mul_of_nonneg_right (hV b) (norm_nonneg _)
theorem bondGradNorm_comp_shift {G : BondField ι → ℝ} (hG : Differentiable ℝ G) (ξ : BondField ι)
    (z : BondField (Complement X)) (b : Complement X) :
    bondGradNorm (fun z => G (ξ + extendByZero X z)) b z = bondGradNorm G b (ξ + extendByZero X z) := by
  unfold bondGradNorm
  rw [fderiv_comp_shift hG]
  congr 1
  ext v
  have e2 : extendByZero X ((ContinuousLinearMap.single ℝ (fun _ : Complement X => BondVector) b) v) =
      bondVariation (b : ι) v := extendByZero_single X b v
  simp only [ContinuousLinearMap.comp_apply, e2]
  rfl
theorem abs_conditionalCovariance_le (hI : covarianceSupNormBound) {m κ : ℝ} {d : ι → ι → ℝ}
    {Ψ G : BondField ι → ℝ} {K : ι → ι → ℝ} {B : ι → ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ)
    (hp : IsCutoff ρ p) (hd : IsPseudoMetricOnBonds d) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K)
    (hG : ContDiff ℝ 1 G)
    (hB : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm G b η ≤ B b)
    {ξ V : BondField ι} (hξ : SupportedInBalls X ρ ξ) (hV0 : ∀ b, b ∉ X → V b = 0)
    (hV : ∀ b, ‖V b‖ ≤ 2 * ρ) :
    |ballCovariance (cutoffFactor ρ p) (fun z => Ψ (ξ + extendByZero X z))
        (fun z => G (ξ + extendByZero X z)) (fun z => fderiv ℝ Ψ (ξ + extendByZero X z) V)| ≤
      m⁻¹ * ∑ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) := by
  have hd' : IsPseudoMetricOnBonds (fun b b' : Complement X => d b b') :=
    ⟨fun b => hd.self b, fun b b' => hd.symm b b', fun b b' b'' => hd.triangle b b' b''⟩
  have hshift : ContDiff ℝ 1 fun z : BondField (Complement X) => ξ + extendByZero X z :=
    contDiff_const.add (extendByZero X).contDiff
  have hfs : ContDiff ℝ 1 fun y => fderiv ℝ Ψ y V :=
    ((hC.smooth.fderiv_right (m := 2) (by norm_num)).of_le (by norm_num)).clm_apply contDiff_const
  refine hI (Complement X) ρ m κ _ _ _ p hρ hm hκ hp hd' (restrict_complement hρ hκ hd hC hξ) _ _
    (fun b => B b) (fun b'' => ∑ b ∈ X, K b'' b * (2 * ρ)) (hG.comp hshift) (hfs.comp hshift) ?_ ?_
  · intro z hz b
    rw [bondGradNorm_comp_shift (hG.differentiable (by norm_num))]
    exact hB _ (shift_norm_lt hξ hz) b
  · intro z hz b
    exact bondGradNorm_directional_le hρ hC hξ hV0 hV z hz b
theorem hasDerivAt_conditionalExpectation {Ψ G : BondField ι → ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)) (hΨ : ContDiff ℝ 3 Ψ)
    (hG : ContDiff ℝ 1 G) (ξ V : BondField ι) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ballExpectation (cutoffFactor ρ p)
        (fun z => Ψ (ξ + t • V + extendByZero X z)) (fun z => G (ξ + t • V + extendByZero X z)))
      (ballExpectation (cutoffFactor ρ p) (fun z => Ψ (ξ + t • V + extendByZero X z))
          (fun z => fderiv ℝ G (ξ + t • V + extendByZero X z) V) -
        ballCovariance (cutoffFactor ρ p) (fun z => Ψ (ξ + t • V + extendByZero X z))
          (fun z => G (ξ + t • V + extendByZero X z))
          (fun z => fderiv ℝ Ψ (ξ + t • V + extendByZero X z) V)) t := by
  set P : ℝ → BondField (Complement X) → BondField ι := fun t z => ξ + t • V + extendByZero X z
    with hPd
  have hΨc : Continuous Ψ := hΨ.continuous
  have hGc : Continuous G := hG.continuous
  have hΨ1 : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdΨ : Continuous fun y => fderiv ℝ Ψ y V :=
    (hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdG : Continuous fun y => fderiv ℝ G y V :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hP : Continuous (Function.uncurry P) := by
    have h1 : Continuous fun y : ℝ × BondField (Complement X) => extendByZero X y.2 :=
      (extendByZero X).continuous.comp continuous_snd
    exact (continuous_const.add (continuous_fst.smul continuous_const)).add h1
  have hPz : ∀ t, Continuous (P t) := fun t => hP.comp (Continuous.prodMk_right t)
  have hline : ∀ t z, HasDerivAt (fun s => P s z) V t := by
    intro t z
    have h1 : HasDerivAt (fun s : ℝ => s • V) V t := by
      simpa using (hasDerivAt_id t).smul_const V
    exact (h1.const_add ξ).add_const (extendByZero X z)
  have hΨl : ∀ t z, HasDerivAt (fun s => Ψ (P s z)) (fderiv ℝ Ψ (P t z) V) t := fun t z =>
    (hΨ1 (P t z)).hasFDerivAt.comp_hasDerivAt t (hline t z)
  have hGl : ∀ t z, HasDerivAt (fun s => G (P s z)) (fderiv ℝ G (P t z) V) t := fun t z =>
    (hG1 (P t z)).hasFDerivAt.comp_hasDerivAt t (hline t z)
  set E : ℝ → BondField (Complement X) → ℝ := fun t z => Real.exp (-Ψ (P t z)) with hE
  have hEc : Continuous (Function.uncurry E) := Real.continuous_exp.comp (hΨc.comp hP).neg
  have hEl : ∀ t z, HasDerivAt (fun s => E s z) (-(fderiv ℝ Ψ (P t z) V) * E t z) t := by
    intro t z
    have := (hΨl t z).neg.exp
    simpa [hE, mul_comm] using this
  set w := radialWeightProd (ι := Complement X) (cutoffFactor ρ p) with hw
  have hwc : Continuous w := continuous_radialWeightProd hr
  have hwk : HasCompactSupport w := hasCompactSupport_radialWeightProd hρ
  have hG2 : Continuous (Function.uncurry fun t z => G (P t z)) := hGc.comp hP
  have hq1 : Continuous (Function.uncurry fun t z => -(fderiv ℝ Ψ (P t z) V) * E t z) :=
    (hdΨ.comp hP).neg.mul hEc
  have hq2 : Continuous (Function.uncurry fun t z => G (P t z) * E t z) := hG2.mul hEc
  have hq3 : Continuous (Function.uncurry fun t z => fderiv ℝ G (P t z) V * E t z +
      G (P t z) * (-(fderiv ℝ Ψ (P t z) V) * E t z)) :=
    ((hdG.comp hP).mul hEc).add (hG2.mul ((hdΨ.comp hP).neg.mul hEc))
  have hD : HasDerivAt (fun t => ∫ z, E t z * w z)
      (∫ z, (-(fderiv ℝ Ψ (P t z) V) * E t z) * w z) t :=
    hasDerivAt_integral_mul_weight hEc hq1 hEl hwc hwk t
  have hN : HasDerivAt (fun t => ∫ z, (G (P t z) * E t z) * w z)
      (∫ z, (fderiv ℝ G (P t z) V * E t z + G (P t z) * (-(fderiv ℝ Ψ (P t z) V) * E t z)) * w z) t :=
    hasDerivAt_integral_mul_weight hq2 hq3 (fun t z => (hGl t z).mul (hEl t z)) hwc hwk t
  have hdens : ∀ t z, ballDensity (cutoffFactor ρ p) (fun z => Ψ (P t z)) z = E t z * w z :=
    fun t z => mul_comm _ _
  have hpos : ∀ t, 0 < ∫ z, E t z * w z := by
    intro t
    have := integral_ballDensity_pos (p := p) hρ hr (Ψ := fun z => Ψ (P t z)) (hΨc.comp (hPz t))
    simpa only [hdens] using this
  have hQ : (fun t : ℝ => ballExpectation (cutoffFactor ρ p) (fun z => Ψ (P t z))
      (fun z => G (P t z))) =
      fun t => (∫ z, (G (P t z) * E t z) * w z) / ∫ z, E t z * w z := by
    funext t
    unfold ballExpectation
    simp only [hdens, mul_assoc]
  have hint : ∀ {h : BondField (Complement X) → ℝ}, Continuous h →
      Integrable fun z => h z * (E t z * w z) := by
    intro h hh
    have := integrable_mul_ballDensity (p := p) hρ hr (Ψ := fun z => Ψ (P t z)) (h := h)
      (hΨc.comp (hPz t)) hh
    simpa only [hdens] using this
  have hcP := hPz t
  have i1 : Integrable fun z => fderiv ℝ G (P t z) V * (E t z * w z) := hint (hdG.comp hcP)
  have i2 : Integrable fun z => (G (P t z) * fderiv ℝ Ψ (P t z) V) * (E t z * w z) :=
    hint ((hGc.comp hcP).mul (hdΨ.comp hcP))
  have hE1 : (∫ z, (fderiv ℝ G (P t z) V * E t z +
        G (P t z) * (-(fderiv ℝ Ψ (P t z) V) * E t z)) * w z) =
      (∫ z, fderiv ℝ G (P t z) V * (E t z * w z)) -
        ∫ z, (G (P t z) * fderiv ℝ Ψ (P t z) V) * (E t z * w z) := by
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only []; ring)
  have hE3 : (∫ z, (-(fderiv ℝ Ψ (P t z) V) * E t z) * w z) =
      -∫ z, fderiv ℝ Ψ (P t z) V * (E t z * w z) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only []; ring)
  have hgoal : (fun t : ℝ => ballExpectation (cutoffFactor ρ p)
      (fun z => Ψ (ξ + t • V + extendByZero X z)) (fun z => G (ξ + t • V + extendByZero X z))) =
      fun t => (∫ z, (G (P t z) * E t z) * w z) / ∫ z, E t z * w z := hQ
  rw [hgoal]
  refine (HasDerivAt.fun_div hN hD (hpos t).ne').congr_deriv ?_
  rw [hE1, hE3]
  have hmean : ∀ h : BondField (Complement X) → ℝ,
      ballExpectation (cutoffFactor ρ p) (fun z => Ψ (ξ + t • V + extendByZero X z)) h =
        (∫ z, h z * (E t z * w z)) / ∫ z, E t z * w z := by
    intro h
    unfold ballExpectation
    have hh : ∀ z, ballDensity (cutoffFactor ρ p) (fun z => Ψ (ξ + t • V + extendByZero X z)) z =
        E t z * w z := hdens t
    simp only [hh]
  have m3 : ballExpectation (cutoffFactor ρ p) (fun z => Ψ (ξ + t • V + extendByZero X z))
      (fun z => G (ξ + t • V + extendByZero X z)) =
      (∫ z, (G (P t z) * E t z) * w z) / ∫ z, E t z * w z := by
    rw [hmean]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hPd]; ring)
  unfold ballCovariance
  rw [m3, hmean (fun z => fderiv ℝ G (ξ + t • V + extendByZero X z) V),
    hmean (fun η => G (ξ + t • V + extendByZero X η) * fderiv ℝ Ψ (ξ + t • V + extendByZero X η) V),
    hmean (fun z => fderiv ℝ Ψ (ξ + t • V + extendByZero X z) V)]
  change _ = (∫ z, fderiv ℝ G (P t z) V * (E t z * w z)) / (∫ z, E t z * w z) -
    ((∫ z, (G (P t z) * fderiv ℝ Ψ (P t z) V) * (E t z * w z)) / (∫ z, E t z * w z) -
      (∫ z, (G (P t z) * E t z) * w z) / (∫ z, E t z * w z) *
        ((∫ z, fderiv ℝ Ψ (P t z) V * (E t z * w z)) / ∫ z, E t z * w z))
  have hne := (hpos t).ne'
  generalize (∫ z, E t z * w z) = Dv at hne ⊢
  generalize (∫ z, (G (P t z) * E t z) * w z) = Nv
  generalize (∫ z, fderiv ℝ G (P t z) V * (E t z * w z)) = E1
  generalize (∫ z, (G (P t z) * fderiv ℝ Ψ (P t z) V) * (E t z * w z)) = E2
  generalize (∫ z, fderiv ℝ Ψ (P t z) V * (E t z * w z)) = E3
  field_simp
  ring
def conditionalExpectation (X : Finset ι) (ρ : ℝ) (p : ℝ → ℝ) (Ψ G : BondField ι → ℝ)
    (ξ : BondField ι) : ℝ :=
  ballExpectation (cutoffFactor ρ p) (fun z => Ψ (ξ + extendByZero X z)) (fun z => G (ξ + extendByZero X z))
theorem SupportedInBalls.segment {ξ ξ' : BondField ι} (h : SupportedInBalls X ρ ξ)
    (h' : SupportedInBalls X ρ ξ') {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    SupportedInBalls X ρ (ξ' + t • (ξ - ξ')) where
  vanishes := by
    intro b hb
    simp [h.vanishes b hb, h'.vanishes b hb]
  norm_lt := by
    intro b hb
    have e : (ξ' + t • (ξ - ξ')) b = (1 - t) • ξ' b + t • ξ b := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, sub_smul, one_smul]
      abel
    rw [e]
    have hc := convex_ball (0 : BondVector) ρ
    have := hc (by simpa using h'.norm_lt b hb) (by simpa using h.norm_lt b hb)
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
    simpa using this
theorem abs_fderiv_apply_le {G : BondField ι → ℝ} {B : ι → ℝ} {ζ V : BondField ι}
    (hB : ∀ b, bondGradNorm G b ζ ≤ B b) (hV0 : ∀ b, b ∉ X → V b = 0) (hV : ∀ b, ‖V b‖ ≤ 2 * ρ) :
    |fderiv ℝ G ζ V| ≤ ∑ b ∈ X, B b * (2 * ρ) := by
  conv_lhs => rw [eq_sum_bondVariation hV0]
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 := ((fderiv ℝ G ζ).comp
    (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)).le_opNorm (V b)
  have h2 : (((fderiv ℝ G ζ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) (V b)) =
      fderiv ℝ G ζ (bondVariation b (V b)) := rfl
  rw [h2, Real.norm_eq_abs] at h1
  refine h1.trans ?_
  exact mul_le_mul (hB b) (hV b) (norm_nonneg _) ((norm_nonneg _).trans (hB b))
theorem abs_conditionalExpectation_sub_le (hI : covarianceSupNormBound) {m κ : ℝ}
    {d : ι → ι → ℝ} {Ψ G : BondField ι → ℝ} {K : ι → ι → ℝ} {B : ι → ℝ} (hρ : 0 < ρ) (hm : 0 < m)
    (hκ : 0 ≤ κ) (hp : IsCutoff ρ p) (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0))
    (hd : IsPseudoMetricOnBonds d) (hC : IsUniformlyConvexDecaying ρ m κ d Ψ K) (hG : ContDiff ℝ 1 G)
    (hB : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm G b η ≤ B b)
    {ξ ξ' : BondField ι} (h : SupportedInBalls X ρ ξ) (h' : SupportedInBalls X ρ ξ') :
    |conditionalExpectation X ρ p Ψ G ξ - conditionalExpectation X ρ p Ψ G ξ'| ≤
      ∑ b ∈ X, B b * (2 * ρ) + m⁻¹ * ∑ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) := by
  set V := ξ - ξ' with hVd
  have hV0 : ∀ b, b ∉ X → V b = 0 := fun b hb => by
    simp [hVd, h.vanishes b hb, h'.vanishes b hb]
  have hV : ∀ b, ‖V b‖ ≤ 2 * ρ := by
    intro b
    by_cases hb : b ∈ X
    · have := norm_sub_le (ξ b) (ξ' b)
      have h1 := h.norm_lt b hb
      have h2 := h'.norm_lt b hb
      simp only [hVd, Pi.sub_apply]
      linarith
    · rw [hV0 b hb, norm_zero]
      positivity
  have hder := fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) =>
    (hasDerivAt_conditionalExpectation (X := X) hρ hr hC.smooth hG ξ' V t).hasDerivWithinAt
      (s := Set.Icc (0 : ℝ) 1)
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖ballExpectation (cutoffFactor ρ p) (fun z => Ψ (ξ' + t • V + extendByZero X z))
          (fun z => fderiv ℝ G (ξ' + t • V + extendByZero X z) V) -
        ballCovariance (cutoffFactor ρ p) (fun z => Ψ (ξ' + t • V + extendByZero X z))
          (fun z => G (ξ' + t • V + extendByZero X z))
          (fun z => fderiv ℝ Ψ (ξ' + t • V + extendByZero X z) V)‖ ≤
      ∑ b ∈ X, B b * (2 * ρ) + m⁻¹ * ∑ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) := by
    intro t ht
    have hon := SupportedInBalls.segment h h' ht
    have hcz : Continuous fun z : BondField (Complement X) => ξ' + t • V + extendByZero X z :=
      continuous_const.add (extendByZero X).continuous
    have c1 := abs_ballExpectation_le (p := p) hρ hr
      (Ψ := fun z => Ψ (ξ' + t • V + extendByZero X z))
      (h := fun z => fderiv ℝ G (ξ' + t • V + extendByZero X z) V) (β := ∑ b ∈ X, B b * (2 * ρ))
      (hC.smooth.continuous.comp hcz)
      (((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp hcz)
      fun z hz => abs_fderiv_apply_le (hB _ (shift_norm_lt hon hz)) hV0 hV
    have c2 := abs_conditionalCovariance_le hI hρ hm hκ hp hd hC hG hB hon hV0 hV
    exact (norm_sub_le _ _).trans (add_le_add c1 c2)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Icc 0 1)
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  simp only [sub_zero, norm_one, mul_one, one_smul, zero_smul, add_zero, hVd,
    add_sub_cancel] at hmv
  rw [Real.norm_eq_abs] at hmv
  exact hmv
def extendFromBlock (x : BondField {b : ι // b ∈ X}) : BondField ι :=
  fun b => if h : b ∈ X then x ⟨b, h⟩ else 0
theorem extendFromBlock_apply_compl (x : BondField {b : ι // b ∈ X}) (b : ι) (hb : b ∉ X) :
    extendFromBlock x b = 0 :=
  dif_neg hb
theorem piEquivPiSubtypeProd_symm_apply_eq (x : BondField {b : ι // b ∈ X})
    (z : BondField (Complement X)) :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => BondVector) (· ∈ X)).symm (x, z) =
      extendFromBlock x + extendByZero X z := by
  funext b
  by_cases hb : b ∈ X
  · have := extendByZero_apply_mem X hb z
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, extendFromBlock, hb, this]
  · have := extendByZero_apply_compl X z ⟨b, hb⟩
    simp only at this
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, extendFromBlock, hb, this]
theorem measurePreserving_splitBlock : MeasurePreserving
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => BondVector) (· ∈ X)) volume
    (volume : Measure (BondField {b : ι // b ∈ X} × BondField (Complement X))) := by
  convert volume_preserving_piEquivPiSubtypeProd (fun _ : ι => BondVector) (· ∈ X)
  all_goals rfl
theorem integrable_comp_split {h : BondField ι → ℝ} (hi : Integrable h) :
    Integrable fun y : BondField {b : ι // b ∈ X} × BondField (Complement X) =>
      h (extendFromBlock y.1 + extendByZero X y.2) := by
  have m2 := (measurePreserving_splitBlock (X := X)).symm _
  have := (m2.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hi
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨x, z⟩ := y
  simp only [Function.comp_apply, piEquivPiSubtypeProd_symm_apply_eq]
theorem integral_eq_integral_split {h : BondField ι → ℝ} (hi : Integrable h) :
    ∫ η, h η = ∫ x : BondField {b : ι // b ∈ X}, ∫ z : BondField (Complement X),
      h (extendFromBlock x + extendByZero X z) := by
  have m2 := (measurePreserving_splitBlock (X := X)).symm _
  rw [← m2.integral_comp' h, ← integral_prod _ (integrable_comp_split hi)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
    obtain ⟨x, z⟩ := y
    simp only [piEquivPiSubtypeProd_symm_apply_eq])
theorem integrable_mul_mul_ballDensity {Ψ T h : BondField ι → ℝ} {β : ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)) (hΨ : Continuous Ψ)
    (hT : Measurable T) (hβ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |T η| ≤ β)
    (hh : Continuous h) :
    Integrable fun η => T η * h η * ballDensity (cutoffFactor ρ p) Ψ η := by
  have hc := continuous_ballDensity hr hΨ (p := p)
  refine Integrable.mono' (g := fun η => β * (|h η| * ballDensity (cutoffFactor ρ p) Ψ η))
    ((integrable_mul_ballDensity hρ hr hΨ hh.abs).const_mul β)
    ((hT.mul hh.measurable).mul hc.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  by_cases h0 : ballDensity (cutoffFactor ρ p) Ψ η = 0
  · simp [h0]
  · have h1 := hβ η (norm_lt_of_ballDensity_ne_zero h0)
    have h2 := ballDensity_nonneg (ρ := ρ) (p := p) Ψ η
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg h2, mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) h2)
theorem abs_integral_mul_sub_le {Ψ G T : BondField ι → ℝ} {c S β : ℝ} (hρ : 0 < ρ)
    (hr : IsRadialCutoff ρ fun u => cutoffFactor ρ p (max u 0)) (hΨ : Continuous Ψ)
    (hGc : Continuous G) (hT : Measurable T)
    (hread : ∀ η η' : BondField ι, (∀ b ∈ X, η b = η' b) → T η = T η')
    (hβ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |T η| ≤ β)
    (hQ : ∀ ξ, SupportedInBalls X ρ ξ → |conditionalExpectation X ρ p Ψ G ξ - c| ≤ S) :
    |∫ η, T η * (G η - c) * ballDensity (cutoffFactor ρ p) Ψ η| ≤
      β * S * ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by
  set ϱ := ballDensity (cutoffFactor ρ p) Ψ with hϱd
  have hϱi : Integrable ϱ :=
    (continuous_ballDensity hr hΨ).integrable_of_hasCompactSupport (hasCompactSupport_ballDensity hρ Ψ)
  have hi1 : Integrable fun η => T η * (G η - c) * ϱ η :=
    integrable_mul_mul_ballDensity hρ hr hΨ hT hβ (hGc.sub continuous_const)
  rw [integral_eq_integral_split (X := X) hi1, integral_eq_integral_split (X := X) hϱi,
    ← integral_const_mul]
  have hi2 : Integrable fun x : BondField {b : ι // b ∈ X} =>
      ∫ z : BondField (Complement X), ϱ (extendFromBlock x + extendByZero X z) :=
    (integrable_comp_split (X := X) hϱi).integral_prod_left
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hi2.const_mul (β * S))
    (Filter.Eventually.of_forall fun x => ?_)
  set ξ := extendFromBlock x with hξd
  have h0 : ∀ b, b ∉ X → ξ b = 0 := extendFromBlock_apply_compl x
  have hz : Continuous fun z : BondField (Complement X) => ξ + extendByZero X z :=
    continuous_const.add (extendByZero X).continuous
  set Ψz : BondField (Complement X) → ℝ := fun z => Ψ (ξ + extendByZero X z) with hΨz
  have hΨzc : Continuous Ψz := hΨ.comp hz
  set g : BondField (Complement X) → ℝ := fun z => G (ξ + extendByZero X z) with hg
  have hgc : Continuous g := hGc.comp hz
  set a := blockWeight X ρ p ξ with ha
  have hT' : ∀ z, T (ξ + extendByZero X z) = T ξ := fun z =>
    hread _ _ fun b hb => shift_apply_mem ξ z hb
  have hs : ∀ z, ϱ (ξ + extendByZero X z) = a * ballDensity (cutoffFactor ρ p) Ψz z := fun z =>
    ballDensity_shift h0 Ψ z
  set D := ∫ z, ballDensity (cutoffFactor ρ p) Ψz z with hD
  set N := ∫ z, g z * ballDensity (cutoffFactor ρ p) Ψz z with hN
  have iN : Integrable fun z => g z * ballDensity (cutoffFactor ρ p) Ψz z :=
    integrable_mul_ballDensity hρ hr hΨzc hgc
  have iD : Integrable (ballDensity (cutoffFactor ρ p) Ψz) :=
    (continuous_ballDensity hr hΨzc).integrable_of_hasCompactSupport
      (hasCompactSupport_ballDensity hρ Ψz)
  have e1 : ∫ z, T (ξ + extendByZero X z) * (G (ξ + extendByZero X z) - c) *
        ϱ (ξ + extendByZero X z) =
      T ξ * a * (N - c * D) := by
    have e : ∀ z, T (ξ + extendByZero X z) * (G (ξ + extendByZero X z) - c) *
        ϱ (ξ + extendByZero X z) =
        T ξ * a * (g z * ballDensity (cutoffFactor ρ p) Ψz z -
          c * ballDensity (cutoffFactor ρ p) Ψz z) := by
      intro z
      rw [hT', hs]
      simp only [hg]
      ring
    simp only [e]
    rw [integral_const_mul, integral_sub iN (iD.const_mul c), integral_const_mul]
  have e2 : ∫ z, ϱ (ξ + extendByZero X z) = a * D := by
    simp only [hs]
    rw [integral_const_mul]
  rw [e1, e2]
  by_cases ha0 : a = 0
  · simp [ha0]
  have hb : ∀ b, b ∈ X → ‖ξ b‖ < ρ := by
    intro b hb
    apply lt_of_cutoffFactor_ne_zero (p := p)
    intro h
    exact ha0 (Finset.prod_eq_zero hb h)
  have hon : SupportedInBalls X ρ ξ := ⟨h0, hb⟩
  have hDp : 0 < D := integral_ballDensity_pos hρ hr hΨzc
  have hq := hQ ξ hon
  have hN1 : |N - c * D| ≤ S * D := by
    have e3 : N - c * D = (N / D - c) * D := by
      field_simp
    rw [e3, abs_mul, abs_of_pos hDp]
    exact mul_le_mul_of_nonneg_right hq hDp.le
  have hTb : |T ξ| ≤ β := by
    apply hβ
    intro b
    by_cases hbX : b ∈ X
    · exact hb b hbX
    · rw [h0 b hbX]
      simpa using hρ
  have ha1 : 0 ≤ a := blockWeight_nonneg ξ
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ha1]
  calc |T ξ| * a * |N - c * D| ≤ β * a * (S * D) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hTb ha1) hN1 (abs_nonneg _)
          (mul_nonneg ((abs_nonneg _).trans hTb) ha1)
    _ = β * S * (a * D) := by ring
theorem oscillation_sum_le {m κ A : ℝ} {d : ι → ι → ℝ} {K : ι → ι → ℝ} {B : ι → ℝ}
    (hρ : 0 < ρ) (hm : 0 < m) (hκ : 0 ≤ κ) (hd : IsPseudoMetricOnBonds d) (hK : ∀ b b', 0 ≤ K b b')
    (hsym : ∀ b b', K b b' = K b' b) (hB : ∀ b, 0 ≤ B b)
    (hA : ∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) :
    ∑ b ∈ X, B b * (2 * ρ) + m⁻¹ * ∑ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) ≤
      2 * ρ * (1 + A) * ∑ b ∈ X, ∑ b', B b' * Real.exp (-(κ * d b b')) := by
  set W : ι → ℝ := fun b => ∑ b', B b' * Real.exp (-(κ * d b b')) with hW
  have hterm : ∀ b b', 0 ≤ B b' * Real.exp (-(κ * d b b')) := fun b b' =>
    mul_nonneg (hB b') (Real.exp_pos _).le
  have h1 : ∀ b, B b ≤ W b := by
    intro b
    have := Finset.single_le_sum (f := fun b' => B b' * Real.exp (-(κ * d b b')))
      (fun b' _ => hterm b b') (Finset.mem_univ b)
    simpa [hd.self] using this
  have h2 : ∀ b ∈ X, ∑ b' : Complement X, ∑ b'' : Complement X,
      B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) ≤ 2 * ρ * (A * m * W b) := by
    intro b hb
    have hAm : 0 ≤ A * m :=
      (Finset.sum_nonneg fun b' _ => mul_nonneg (hK _ _) (Real.exp_pos _).le).trans (hA b)
    have h3 : ∀ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) ≤
        2 * ρ * (A * m) * (B b' * Real.exp (-(κ * d b b'))) := by
      intro b'
      have h4 : ∀ b'' : Complement X, B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) ≤
          2 * ρ * (B b' * Real.exp (-(κ * d b b'))) * (K b b'' * Real.exp (κ * d b b'')) := by
        intro b''
        have h5 : Real.exp (-(κ * d b' b'')) ≤
            Real.exp (-(κ * d b b')) * Real.exp (κ * d b b'') := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have := hd.triangle b b'' b'
          have e := hd.symm b'' b'
          have := mul_le_mul_of_nonneg_left this hκ
          rw [e] at this
          linarith
        have h6 := mul_le_mul_of_nonneg_left h5
          (mul_nonneg (hB b') (mul_nonneg (hK b b'') (by positivity : 0 ≤ 2 * ρ)))
        rw [hsym b'' b]
        calc _ = B b' * (K b b'' * (2 * ρ)) * Real.exp (-(κ * d b' b'')) := by ring
          _ ≤ _ := h6
          _ = _ := by ring
      refine (Finset.sum_le_sum fun b'' _ => h4 b'').trans ?_
      rw [← Finset.mul_sum]
      have h7 : ∑ b'' : Complement X, K b b'' * Real.exp (κ * d b b'') ≤ A * m := by
        refine le_trans ?_ (hA b)
        rw [sum_complement X (fun b'' => K b b'' * Real.exp (κ * d b b''))]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          simp only [Finset.mem_compl] at hc
          exact Finset.mem_erase.mpr ⟨fun h => hc (h ▸ hb), Finset.mem_univ c⟩
        · exact fun c _ _ => mul_nonneg (hK _ _) (Real.exp_pos _).le
      calc _ ≤ 2 * ρ * (B b' * Real.exp (-(κ * d b b'))) * (A * m) :=
            mul_le_mul_of_nonneg_left h7 (mul_nonneg (by positivity) (hterm b b'))
        _ = _ := by ring
    refine (Finset.sum_le_sum fun b' _ => h3 b').trans ?_
    rw [← Finset.mul_sum]
    have h8 : ∑ b' : Complement X, B b' * Real.exp (-(κ * d b b')) ≤ W b :=
      sum_complement_le X (f := fun b' => B b' * Real.exp (-(κ * d b b'))) fun b' => hterm b b'
    calc _ ≤ 2 * ρ * (A * m) * W b := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = _ := by ring
  have e1 : ∑ b' : Complement X, ∑ b'' : Complement X,
      B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) =
      ∑ b ∈ X, ∑ b' : Complement X, ∑ b'' : Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) := by
    calc _ = ∑ b' : Complement X, ∑ b'' : Complement X, ∑ b ∈ X,
          B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) := by
          simp only [Finset.mul_sum]
      _ = ∑ b' : Complement X, ∑ b ∈ X, ∑ b'' : Complement X,
          B b' * Real.exp (-(κ * d b' b'')) * (K b'' b * (2 * ρ)) :=
          Finset.sum_congr rfl fun b' _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have h9 : m⁻¹ * ∑ b' : Complement X, ∑ b'' : Complement X,
      B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) ≤
      2 * ρ * A * ∑ b ∈ X, W b := by
    rw [e1]
    have h11 := Finset.sum_le_sum h2
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h11
    calc _ ≤ m⁻¹ * (2 * ρ * (A * m * ∑ b ∈ X, W b)) :=
          mul_le_mul_of_nonneg_left h11 (inv_nonneg.mpr hm.le)
      _ = _ := by
          field_simp
  have h10 : ∑ b ∈ X, B b * (2 * ρ) ≤ 2 * ρ * ∑ b ∈ X, W b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (h1 b) (by positivity)
  have e2 : 2 * ρ * (1 + A) * ∑ b ∈ X, W b =
      2 * ρ * ∑ b ∈ X, W b + 2 * ρ * A * ∑ b ∈ X, W b := by ring
  rw [e2]
  exact add_le_add h10 h9
end Block
end LocalCovariance
open LocalCovariance in
theorem covarianceLocalMeasurableBound_holds (hI : covarianceSupNormBound)
    (hrim : CutoffFactorIsRadialCutoff) : covarianceLocalMeasurableBound := by
  intro ι _ _ ρ m κ A O d Ψ K p hρ hm hκ hp hd hC hA X F G B hF hread hosc hG hB
  have hr := hrim ρ p hρ hp
  have h0 : ∀ b, ‖(0 : BondField ι) b‖ < ρ := fun b => by simpa using hρ
  have hB0 : ∀ b, 0 ≤ B b := fun b => (norm_nonneg _).trans (hB 0 h0 b)
  have hO0 : 0 ≤ O := (abs_nonneg _).trans (hosc 0 0 h0 h0)
  have hΨ : Continuous Ψ := hC.smooth.continuous
  have hGc : Continuous G := hG.continuous
  have hon0 : SupportedInBalls X ρ (0 : BondField ι) := ⟨fun _ _ => rfl, fun b _ => h0 b⟩
  set c := conditionalExpectation X ρ p Ψ G 0 with hc
  set φ := F 0 with hφ
  set S := ∑ b ∈ X, B b * (2 * ρ) + m⁻¹ * ∑ b' : LocalCovariance.Complement X,
      ∑ b'' : LocalCovariance.Complement X,
        B b' * Real.exp (-(κ * d b' b'')) * ∑ b ∈ X, K b'' b * (2 * ρ) with hS
  have hQ : ∀ ξ, SupportedInBalls X ρ ξ → |conditionalExpectation X ρ p Ψ G ξ - c| ≤ S :=
    fun ξ hξ => abs_conditionalExpectation_sub_le hI hρ hm hκ hp hr hd hC hG hB hξ hon0
  have hSle := oscillation_sum_le (X := X) hρ hm hκ hd (kernel_nonneg hρ hC) hC.symm hB0 hA
  set ϱ := ballDensity (cutoffFactor ρ p) Ψ with hϱd
  have hZ : 0 < ∫ η, ϱ η := integral_ballDensity_pos hρ hr hΨ
  set Z := ∫ η, ϱ η with hZd
  have hϱi : Integrable ϱ :=
    (continuous_ballDensity hr hΨ).integrable_of_hasCompactSupport (hasCompactSupport_ballDensity hρ Ψ)
  have hF1 : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |F η - φ| ≤ O := fun η hη => hosc η 0 hη h0
  have hF2 : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |F η| ≤ |φ| + O := by
    intro η hη
    have h1 := hF1 η hη
    have h2 := abs_sub_abs_le_abs_sub (F η) φ
    linarith
  have hmT : Measurable fun η => F η - φ := hF.sub measurable_const
  have t1 := abs_integral_mul_sub_le (X := X) (c := c) (S := S) hρ hr hΨ hGc hmT
    (fun η η' h => by simp only [hread η η' h]) hF1 hQ
  have t2 := abs_integral_mul_sub_le (X := X) (T := fun _ => (1 : ℝ)) (β := 1) (c := c) (S := S)
    hρ hr hΨ hGc measurable_const (fun _ _ _ => rfl) (fun _ _ => by simp) hQ
  have t3 : |∫ η, (F η - φ) * ϱ η| ≤ O * Z := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hϱi.const_mul O)
    refine Filter.Eventually.of_forall fun η => ?_
    by_cases h : ϱ η = 0
    · simp [h]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (ballDensity_nonneg Ψ η)]
      exact mul_le_mul_of_nonneg_right (hF1 η (norm_lt_of_ballDensity_ne_zero h))
        (ballDensity_nonneg Ψ η)
  have iFG : Integrable fun η => F η * G η * ϱ η := integrable_mul_mul_ballDensity hρ hr hΨ hF hF2 hGc
  have iF : Integrable fun η => F η * ϱ η := by
    simpa using integrable_mul_mul_ballDensity (h := fun _ => (1 : ℝ)) hρ hr hΨ hF hF2 continuous_const
  have iG : Integrable fun η => G η * ϱ η := integrable_mul_ballDensity hρ hr hΨ hGc
  set I1 := ∫ η, F η * G η * ϱ η with hI1
  set I2 := ∫ η, F η * ϱ η with hI2
  set I3 := ∫ η, G η * ϱ η with hI3
  have a1 : ∫ η, (F η - φ) * (G η - c) * ϱ η = I1 - c * I2 - φ * I3 + c * φ * Z := by
    have e : ∀ η, (F η - φ) * (G η - c) * ϱ η =
        F η * G η * ϱ η - c * (F η * ϱ η) - φ * (G η * ϱ η) + c * φ * ϱ η := fun η => by ring
    simp only [e]
    have j1 : Integrable fun η => F η * G η * ϱ η - c * (F η * ϱ η) := iFG.sub (iF.const_mul c)
    have j2 : Integrable fun η => F η * G η * ϱ η - c * (F η * ϱ η) - φ * (G η * ϱ η) :=
      j1.sub (iG.const_mul φ)
    rw [integral_add j2 (hϱi.const_mul (c * φ)), integral_sub j1 (iG.const_mul φ),
      integral_sub iFG (iF.const_mul c), integral_const_mul, integral_const_mul, integral_const_mul]
  have a2 : ∫ η, (F η - φ) * ϱ η = I2 - φ * Z := by
    have e : ∀ η, (F η - φ) * ϱ η = F η * ϱ η - φ * ϱ η := fun η => by ring
    simp only [e]
    rw [integral_sub iF (hϱi.const_mul φ), integral_const_mul]
  have a3 : ∫ η, (1 : ℝ) * (G η - c) * ϱ η = I3 - c * Z := by
    have e : ∀ η, (1 : ℝ) * (G η - c) * ϱ η = G η * ϱ η - c * ϱ η := fun η => by ring
    simp only [e]
    rw [integral_sub iG (hϱi.const_mul c), integral_const_mul]
  rw [a1] at t1
  rw [a2] at t3
  rw [a3] at t2
  have hcov : ballCovariance (cutoffFactor ρ p) Ψ F G = I1 / Z - I2 / Z * (I3 / Z) := rfl
  have e4 : I1 / Z - I2 / Z * (I3 / Z) =
      ((I1 - c * I2 - φ * I3 + c * φ * Z) * Z - (I2 - φ * Z) * (I3 - c * Z)) / Z ^ 2 := by
    field_simp
    ring
  rw [hcov, e4, abs_div, abs_of_pos (by positivity : 0 < Z ^ 2), div_le_iff₀ (by positivity)]
  have b1 : |(I1 - c * I2 - φ * I3 + c * φ * Z) * Z| ≤ O * S * Z * Z := by
    rw [abs_mul, abs_of_pos hZ]
    exact mul_le_mul_of_nonneg_right t1 hZ.le
  have b2 : |(I2 - φ * Z) * (I3 - c * Z)| ≤ O * Z * (1 * S * Z) := by
    rw [abs_mul]
    exact mul_le_mul t3 t2 (abs_nonneg _) (by positivity)
  have b3 := abs_sub ((I1 - c * I2 - φ * I3 + c * φ * Z) * Z) ((I2 - φ * Z) * (I3 - c * Z))
  have hfin : 2 * O * S ≤ 4 * ρ * (1 + A) * O *
      ∑ b ∈ X, ∑ b', B b' * Real.exp (-(κ * d b b')) := by
    have := mul_le_mul_of_nonneg_left hSle (by positivity : 0 ≤ 2 * O)
    calc 2 * O * S ≤ _ := this
      _ = _ := by ring
  calc _ ≤ O * S * Z * Z + O * Z * (1 * S * Z) := b3.trans (add_le_add b1 b2)
    _ = 2 * O * S * Z ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin (by positivity)
end YangMills.Construction.ConvexMeasures
end
