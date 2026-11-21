import YangMills.Construction.LawByMomentsOfTheFlow.GaussianAgainstACutLaw
import YangMills.Construction.ResponseInTheExpansion.LawNearAHessianProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ConvexObservables YangMills.Construction.WeightedResponses
namespace YangMills.Construction.MomentMethod
section StandardGaussian
variable {J : Type} [Fintype J] [DecidableEq J]
private theorem pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : J => gaussianReal 0 1) =
      (volume : Measure (J → ℝ)).withDensity fun x => ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (x j)) := by
  refine Measure.pi_eq fun s hs => ?_
  have hint : ∀ j, Integrable ((s j).indicator (gaussianPDFReal 0 1)) volume := fun j =>
    (integrable_gaussianPDFReal 0 1).indicator (hs j)
  have hp : ∀ x : J → ℝ, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (x j))) x =
      ENNReal.ofReal (∏ j, (s j).indicator (gaussianPDFReal 0 1) (x j)) := fun x => by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Set.indicator_of_mem (hx j (Set.mem_univ j))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨j, hj⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _), ENNReal.ofReal_zero]
  have hnn : ∀ j t, 0 ≤ (s j).indicator (gaussianPDFReal 0 1) t := fun j t =>
    Set.indicator_nonneg (fun t _ => gaussianPDFReal_nonneg 0 1 t) t
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hp]
  have hi : Integrable (fun x : J → ℝ => ∏ j, (s j).indicator (gaussianPDFReal 0 1) (x j)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j _ => hnn j _),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg fun j _ => integral_nonneg (hnn j)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [gaussianReal_apply 0 (by norm_num), integral_indicator (hs j),
    ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (Filter.Eventually.of_forall fun t => gaussianPDFReal_nonneg 0 1 t)]
  rfl
private def standardDensity (x : J → ℝ) : ℝ := ∏ j, gaussianPDFReal 0 1 (x j)
private theorem standardDensity_eq (x : J → ℝ) :
    standardDensity x = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card J * Real.exp ((-(1 / 2) : ℝ) * ∑ j, x j * x j) := by
  have h : ∀ t : ℝ, gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp ((-(1 / 2) : ℝ) * (t * t)) := fun t => by
    unfold gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  unfold standardDensity
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, Finset.mul_sum]
private theorem hasFDerivAt_standardDensity (x : J → ℝ) :
    HasFDerivAt standardDensity ((-standardDensity x) • ∑ j, x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ)) x := by
  have h1 : ∀ j, HasFDerivAt (fun y : J → ℝ => y j * y j)
      (x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ) + x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ)) x :=
    fun j => (hasFDerivAt_apply j x).mul (hasFDerivAt_apply j x)
  have h2 : HasFDerivAt (fun y : J → ℝ => ∑ j, y j * y j)
      (∑ j, (x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ) + x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ))) x :=
    HasFDerivAt.fun_sum fun j _ => h1 j
  have h3 := ((h2.const_mul (-(1 / 2) : ℝ)).exp).const_mul ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card J)
  have e : standardDensity = fun y : J → ℝ => (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card J * Real.exp ((-(1 / 2) : ℝ) * ∑ j, y j * y j) :=
    funext standardDensity_eq
  have e2 : (-standardDensity x) • ∑ j, x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card J • Real.exp ((-(1 / 2) : ℝ) * ∑ j, x j * x j) • (-(1 / 2) : ℝ) •
        ∑ j, (x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ) + x j • (ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ)) := by
    rw [standardDensity_eq, Finset.sum_add_distrib, ← two_smul ℝ, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [e2]
  rw [e]
  exact h3
private theorem differentiable_standardDensity : Differentiable ℝ (standardDensity : (J → ℝ) → ℝ) := fun x =>
  (hasFDerivAt_standardDensity x).differentiableAt
private theorem fderiv_standardDensity (x v : J → ℝ) :
    fderiv ℝ standardDensity x v = -(standardDensity x * ∑ j, x j * v j) := by
  rw [(hasFDerivAt_standardDensity x).fderiv]
  simp [smul_eq_mul, ContinuousLinearMap.sum_apply]
private theorem standardDensity_nonneg (x : J → ℝ) : 0 ≤ standardDensity x :=
  Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg 0 1 _
private theorem measurable_standardDensity : Measurable (standardDensity : (J → ℝ) → ℝ) :=
  Finset.measurable_prod _ fun j _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply j)
private theorem measurable_ofReal_standardDensity :
    Measurable fun x : J → ℝ => ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (x j)) :=
  ENNReal.measurable_ofReal.comp measurable_standardDensity
private theorem integral_stdGaussian_eq (h : EuclideanSpace ℝ J → ℝ) (hc : Continuous h) :
    ∫ w, h w ∂stdGaussian (EuclideanSpace ℝ J) = ∫ x : J → ℝ, standardDensity x * h (WithLp.toLp 2 x) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hc.aestronglyMeasurable, pi_gaussianReal_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul measurable_ofReal_standardDensity
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [show (ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (x j))).toReal = standardDensity x from
    ENNReal.toReal_ofReal (standardDensity_nonneg x)]
private theorem integrable_standardDensity_mul (h : EuclideanSpace ℝ J → ℝ) (hc : Continuous h)
    (hi : Integrable h (stdGaussian (EuclideanSpace ℝ J))) :
    Integrable (fun x : J → ℝ => standardDensity x * h (WithLp.toLp 2 x)) volume := by
  rw [← map_pi_eq_stdGaussian] at hi
  have h1 := (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).1 hi
  rw [pi_gaussianReal_eq_withDensity, integrable_withDensity_iff_integrable_smul' measurable_ofReal_standardDensity
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, Function.comp]
  rw [show (ENNReal.ofReal (∏ j, gaussianPDFReal 0 1 (x j))).toReal = standardDensity x from
    ENNReal.toReal_ofReal (standardDensity_nonneg x)]
end StandardGaussian
section PolynomialMoments
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [CompleteSpace H]
private theorem integrable_one_add_norm_pow (ν : Measure H) [IsGaussian ν] (m : ℕ) :
    Integrable (fun w => (1 + ‖w‖) ^ m) ν := by
  have h1 : MemLp (id : H → H) ((m + 1 : ℕ) : ENNReal) ν := IsGaussian.memLp_id ν _ (by simp)
  have h1n : MemLp (fun w : H => ‖w‖) ((m + 1 : ℕ) : ENNReal) ν := h1.norm
  have h2 : MemLp (fun w : H => 1 + ‖w‖) ((m + 1 : ℕ) : ENNReal) ν := MemLp.add (memLp_const (1 : ℝ)) h1n
  have h3 := h2.integrable_norm_pow (Nat.succ_ne_zero m)
  refine h3.mono' ((continuous_const.add continuous_norm).pow m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  have hw : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_right₀ hw (Nat.le_succ m)
abbrev _root_.YangMills.SharedProofs.p133249 := @integrable_one_add_norm_pow
private theorem integrable_of_polynomial_bound (ν : Measure H) [IsGaussian ν] (h : H → ℝ) (hc : Continuous h) (C : ℝ)
    (m : ℕ) (hb : ∀ w, |h w| ≤ C * (1 + ‖w‖) ^ m) : Integrable h ν :=
  ((integrable_one_add_norm_pow ν m).const_mul C).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hb w)
end PolynomialMoments
section SteinIdentity
variable {J : Type} [Fintype J] [DecidableEq J]
private theorem stein_stdGaussian (f : EuclideanSpace ℝ J → ℝ) (hf : Differentiable ℝ f) (hdc : Continuous (fderiv ℝ f))
    (C : ℝ) (m : ℕ) (h0 : ∀ w, |f w| ≤ C * (1 + ‖w‖) ^ m) (h1 : ∀ w, ‖fderiv ℝ f w‖ ≤ C * (1 + ‖w‖) ^ m)
    (a : EuclideanSpace ℝ J) :
    ∫ w, inner ℝ w a * f w ∂stdGaussian (EuclideanSpace ℝ J) = ∫ w, fderiv ℝ f w a ∂stdGaussian (EuclideanSpace ℝ J) := by
  have hfc : Continuous f := hf.continuous
  set Lm : (J → ℝ) →L[ℝ] EuclideanSpace ℝ J :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)).symm.toContinuousLinearMap with hLm
  have hL : ∀ x, Lm x = WithLp.toLp 2 x := fun x => rfl
  have c₁ : Continuous fun w : EuclideanSpace ℝ J => inner ℝ w a * f w := (continuous_id.inner continuous_const).mul hfc
  have c₂ : Continuous fun w : EuclideanSpace ℝ J => fderiv ℝ f w a := hdc.clm_apply continuous_const
  have i₀ : Integrable f (stdGaussian (EuclideanSpace ℝ J)) := integrable_of_polynomial_bound _ f hfc C m h0
  have i₁ : Integrable (fun w : EuclideanSpace ℝ J => inner ℝ w a * f w) (stdGaussian (EuclideanSpace ℝ J)) := by
    refine integrable_of_polynomial_bound _ _ c₁ (‖a‖ * C) (m + 1) fun w => ?_
    rw [abs_mul]
    have e1 : |inner ℝ w a| ≤ ‖a‖ * (1 + ‖w‖) := by
      have := abs_real_inner_le_norm w a
      nlinarith [norm_nonneg a, norm_nonneg w]
    calc |inner ℝ w a| * |f w| ≤ (‖a‖ * (1 + ‖w‖)) * (C * (1 + ‖w‖) ^ m) := by gcongr; exact h0 w
      _ = _ := by ring
  have i₂ : Integrable (fun w : EuclideanSpace ℝ J => fderiv ℝ f w a) (stdGaussian (EuclideanSpace ℝ J)) := by
    refine integrable_of_polynomial_bound _ _ c₂ (‖a‖ * C) m fun w => ?_
    calc |fderiv ℝ f w a| ≤ ‖fderiv ℝ f w‖ * ‖a‖ := (fderiv ℝ f w).le_opNorm a
      _ ≤ (C * (1 + ‖w‖) ^ m) * ‖a‖ := by gcongr; exact h1 w
      _ = _ := by ring
  have j₀ := integrable_standardDensity_mul f hfc i₀
  have j₁ := integrable_standardDensity_mul _ c₁ i₁
  have j₂ := integrable_standardDensity_mul _ c₂ i₂
  rw [integral_stdGaussian_eq _ c₁, integral_stdGaussian_eq _ c₂]
  have hder : ∀ x : J → ℝ, fderiv ℝ (f ∘ Lm) x (WithLp.ofLp a) = fderiv ℝ f (WithLp.toLp 2 x) a := fun x => by
    have h2 : HasFDerivAt (f ∘ Lm) ((fderiv ℝ f (Lm x)).comp Lm) x := (hf (Lm x)).hasFDerivAt.comp x Lm.hasFDerivAt
    rw [h2.fderiv]
    rfl
  have hin : ∀ x : J → ℝ, inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ J) a = ∑ j, x j * WithLp.ofLp a j := fun x => by
    simp [PiLp.inner_apply, mul_comm]
  have hbp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (J → ℝ))) (f := f ∘ Lm)
    (g := standardDensity) (v := WithLp.ofLp a) ?_ ?_ ?_ (fun x _ => (hf.comp Lm.differentiable) x)
    (fun x _ => differentiable_standardDensity x)
  · have e1 : ∀ x : J → ℝ, (f ∘ Lm) x * fderiv ℝ standardDensity x (WithLp.ofLp a) =
        -(standardDensity x * (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ J) a * f (WithLp.toLp 2 x))) := fun x => by
      rw [fderiv_standardDensity, hin]
      simp only [Function.comp, hL]
      ring
    have e2 : ∀ x : J → ℝ, fderiv ℝ (f ∘ Lm) x (WithLp.ofLp a) * standardDensity x =
        standardDensity x * fderiv ℝ f (WithLp.toLp 2 x) a := fun x => by
      rw [hder, mul_comm]
    simp only [e1, e2] at hbp
    rw [integral_neg] at hbp
    linarith
  · refine j₂.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hder]
    ring
  · refine j₁.neg.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.neg_apply, Function.comp, hL]
    rw [fderiv_standardDensity, hin]
    ring
  · refine j₀.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, hL]
    ring
open scoped MatrixOrder Matrix.Norms.L2Operator in
private theorem stein_multivariateGaussian (G : Matrix J J ℝ) (hG : G.PosSemidef) (Φ : EuclideanSpace ℝ J → ℝ)
    (hΦ : Differentiable ℝ Φ) (hdc : Continuous (fderiv ℝ Φ)) (C : ℝ) (m : ℕ) (h0 : ∀ w, |Φ w| ≤ C * (1 + ‖w‖) ^ m)
    (h1 : ∀ w, ‖fderiv ℝ Φ w‖ ≤ C * (1 + ‖w‖) ^ m) (j : J) :
    ∫ ζ, ζ j * Φ ζ ∂multivariateGaussian 0 G =
      ∫ ζ, fderiv ℝ Φ ζ (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1)) ∂multivariateGaussian 0 G := by
  have hC : 0 ≤ C := by
    have := le_trans (abs_nonneg _) (h0 0)
    have hp : (0 : ℝ) < (1 + ‖(0 : EuclideanSpace ℝ J)‖) ^ m := by positivity
    exact nonneg_of_mul_nonneg_left this hp
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt G) with hT
  have hself : IsSelfAdjoint T := (CFC.sqrt_nonneg G).isSelfAdjoint.map _
  have hTT : T (T (EuclideanSpace.single j 1)) = Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1) := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hT, ← map_mul, CFC.sqrt_mul_sqrt_self _ hG.nonneg]
  have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ J => (0 : EuclideanSpace ℝ J) + T x)
      (stdGaussian (EuclideanSpace ℝ J)) := by
    fun_prop
  have hΦc : Continuous Φ := hΦ.continuous
  have c₁ : Continuous fun ζ : EuclideanSpace ℝ J => ζ j * Φ ζ := by
    refine Continuous.mul ?_ hΦc
    fun_prop
  have c₂ : Continuous fun ζ : EuclideanSpace ℝ J =>
      fderiv ℝ Φ ζ (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1)) :=
    hdc.clm_apply continuous_const
  unfold multivariateGaussian
  rw [integral_map hmeas c₁.aestronglyMeasurable, integral_map hmeas c₂.aestronglyMeasurable]
  simp only [zero_add]
  have hfd : ∀ w, HasFDerivAt (Φ ∘ T) ((fderiv ℝ Φ (T w)).comp T) w := fun w =>
    (hΦ (T w)).hasFDerivAt.comp w T.hasFDerivAt
  have hfd' : fderiv ℝ (Φ ∘ T) = fun w => (fderiv ℝ Φ (T w)).comp T := funext fun w => (hfd w).fderiv
  have hgrow : ∀ w, (1 + ‖T w‖) ^ m ≤ (1 + ‖T‖) ^ m * (1 + ‖w‖) ^ m := fun w => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have := T.le_opNorm w
    nlinarith [norm_nonneg T, norm_nonneg w]
  have hst := stein_stdGaussian (Φ ∘ T) (hΦ.comp T.differentiable) (by
      rw [hfd']
      exact (hdc.comp T.continuous).clm_comp continuous_const)
    (C * (1 + ‖T‖) ^ m * (1 + ‖T‖)) m (fun w => ?_) (fun w => ?_) (T (EuclideanSpace.single j 1))
  · have e1 : ∀ w : EuclideanSpace ℝ J, inner ℝ w (T (EuclideanSpace.single j 1)) = (T w) j := fun w => by
      have := ContinuousLinearMap.adjoint_inner_left T w (EuclideanSpace.single j (1 : ℝ))
      rw [hself.adjoint_eq] at this
      rw [real_inner_comm, this]
      simp [EuclideanSpace.inner_single_left]
    simp only [e1, hfd'] at hst
    simpa [hTT] using hst
  · have hT0 : (1 : ℝ) ≤ 1 + ‖T‖ := by linarith [norm_nonneg T]
    have hp : (0 : ℝ) ≤ (1 + ‖T‖) ^ m * (1 + ‖w‖) ^ m := by positivity
    calc |(Φ ∘ T) w| ≤ C * (1 + ‖T w‖) ^ m := h0 _
      _ ≤ C * ((1 + ‖T‖) ^ m * (1 + ‖w‖) ^ m) := by gcongr; exact hgrow w
      _ ≤ C * ((1 + ‖T‖) ^ m * (1 + ‖w‖) ^ m) * (1 + ‖T‖) := le_mul_of_one_le_right (by positivity) hT0
      _ = _ := by ring
  · have hT0 : ‖T‖ ≤ 1 + ‖T‖ := by linarith
    rw [hfd']
    calc ‖(fderiv ℝ Φ (T w)).comp T‖ ≤ ‖fderiv ℝ Φ (T w)‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (1 + ‖T w‖) ^ m) * (1 + ‖T‖) := by gcongr; exact h1 _
      _ ≤ (C * ((1 + ‖T‖) ^ m * (1 + ‖w‖) ^ m)) * (1 + ‖T‖) := by gcongr; exact hgrow w
      _ = _ := by ring
end SteinIdentity
section BondFields
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fieldOfCoordinates
      map_add' := fun a b => by
        funext c
        ext e
        simp [fieldOfCoordinates]
      map_smul' := fun r a => by
        funext c
        ext e
        simp [fieldOfCoordinates] }
private theorem fieldOfCoordinatesCLM_apply (ζ : EuclideanSpace ℝ (Fin 3 × ι)) :
    fieldOfCoordinatesCLM ζ = fieldOfCoordinates ζ := rfl
private theorem bondField_eq_sum (κ : BondField ι) : κ = ∑ j : Fin 3 × ι, (κ j.2 j.1) • unitVariation j := by
  funext b
  ext e
  rw [Finset.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e, Finset.sum_eq_single b]
  · simp [unitVariation, bondVariation]
  · intro b' _ hb
    simp [unitVariation, bondVariation, Pi.single_eq_of_ne hb.symm]
  · simp
  · intro e' _ he
    refine Finset.sum_eq_zero fun b' _ => ?_
    by_cases hb : b' = b
    · subst hb
      simp [unitVariation, bondVariation, he.symm]
    · simp [unitVariation, bondVariation, Pi.single_eq_of_ne (Ne.symm hb)]
  · simp
private theorem clm_apply_eq_sum (l : BondField ι →L[ℝ] ℝ) (κ : BondField ι) :
    l κ = ∑ j : Fin 3 × ι, κ j.2 j.1 * l (unitVariation j) := by
  conv_lhs => rw [bondField_eq_sum κ]
  simp [map_sum, map_smul]
private theorem cutoffRadialDeriv_add (p : ℝ → ℝ) (e v w : BondVector) :
    cutoffRadialDeriv p e (v + w) = cutoffRadialDeriv p e v + cutoffRadialDeriv p e w := by
  simp only [cutoffRadialDeriv, inner_add_right]
  ring
private theorem cutoffRadialDeriv_smul (p : ℝ → ℝ) (e v : BondVector) (c : ℝ) :
    cutoffRadialDeriv p e (c • v) = c * cutoffRadialDeriv p e v := by
  simp only [cutoffRadialDeriv, inner_smul_right]
  ring
private theorem cutoffRadialDeriv_zero (p : ℝ → ℝ) (e : BondVector) : cutoffRadialDeriv p e 0 = 0 := by
  simp [cutoffRadialDeriv]
private theorem cutoffRadialDeriv_eq_sum (p : ℝ → ℝ) (e v : BondVector) :
    cutoffRadialDeriv p e v = ∑ c : Fin 3, v c * cutoffRadialDeriv p e (EuclideanSpace.single c 1) := by
  have h : v = ∑ c : Fin 3, v c • (EuclideanSpace.single c (1 : ℝ) : BondVector) := by
    ext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  have hs : ∀ (S : Finset (Fin 3)) (f : Fin 3 → BondVector),
      cutoffRadialDeriv p e (∑ c ∈ S, f c) = ∑ c ∈ S, cutoffRadialDeriv p e (f c) := by
    intro S f
    induction S using Finset.induction_on with
    | empty => simp [cutoffRadialDeriv_zero]
    | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cutoffRadialDeriv_add, ih]
  rw [hs]
  exact Finset.sum_congr rfl fun c _ => cutoffRadialDeriv_smul p e _ _
private theorem fderiv_add_cutoff_eq_sum_gradientCoord (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η κ : BondField ι) :
    fderiv ℝ Ψ η κ + ∑ b, cutoffRadialDeriv p (η b) (κ b) = ∑ i : Fin 3 × ι, κ i.2 i.1 * gradientCoord p Ψ η i := by
  simp only [gradientCoord, mul_add, Finset.sum_add_distrib]
  rw [← clm_apply_eq_sum]
  congr 1
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact cutoffRadialDeriv_eq_sum p _ _
private def rotatedPoint (θ : ℝ) (η : BondField ι) (ζ : EuclideanSpace ℝ (Fin 3 × ι)) : BondField ι :=
  Real.cos θ • η + Real.sin θ • fieldOfCoordinatesCLM ζ
private theorem one_add_norm_rotatedPoint (θ : ℝ) (η : BondField ι) (ζ : EuclideanSpace ℝ (Fin 3 × ι)) :
    1 + ‖rotatedPoint θ η ζ‖ ≤
      (1 + ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖) * ((1 + ‖η‖) * (1 + ‖ζ‖)) := by
  have h1 : ‖rotatedPoint θ η ζ‖ ≤
      ‖η‖ + ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖ * ‖ζ‖ := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)
    · rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)) (fieldOfCoordinatesCLM.le_opNorm ζ)
  have a := norm_nonneg η
  have b := norm_nonneg ζ
  have c := norm_nonneg (fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)
  nlinarith [mul_nonneg a b, mul_nonneg c a, mul_nonneg c b, mul_nonneg (mul_nonneg c a) b]
variable (F : BondField ι → ℝ) (hF : ContDiff ℝ 2 F) (Cg : ℝ) (k : ℕ)
  (hgrow : ∀ η, ∀ l : ℕ, l ≤ 2 → ‖iteratedFDeriv ℝ l F η‖ ≤ Cg * (1 + ‖η‖) ^ k)
include hF in
private theorem contDiff_one_fderiv : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
include hgrow in
private theorem abs_le_growth (η : BondField ι) : |F η| ≤ Cg * (1 + ‖η‖) ^ k := by
  have := hgrow η 0 (by norm_num)
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
include hgrow in
private theorem norm_fderiv_le_growth (η : BondField ι) : ‖fderiv ℝ F η‖ ≤ Cg * (1 + ‖η‖) ^ k := by
  have := hgrow η 1 (by norm_num)
  rwa [norm_iteratedFDeriv_one] at this
include hgrow in
private theorem norm_fderiv_fderiv_le_growth (η : BondField ι) : ‖fderiv ℝ (fderiv ℝ F) η‖ ≤ Cg * (1 + ‖η‖) ^ k := by
  have := hgrow η 2 (by norm_num)
  rwa [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
include hgrow in
private theorem growthConst_nonneg : 0 ≤ Cg := by
  have h := le_trans (norm_nonneg _) (hgrow 0 0 (by norm_num))
  have hp : (0 : ℝ) < (1 + ‖(0 : BondField ι)‖) ^ k := by positivity
  exact nonneg_of_mul_nonneg_left h hp
include hF hgrow in
private theorem stein_along_rotation (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (hG : G.PosSemidef) (θ : ℝ) (η : BondField ι)
    (j : Fin 3 × ι) :
    ∫ ζ, ζ j * fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j) ∂multivariateGaussian 0 G =
      Real.sin θ * ∫ ζ, fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)
        (fieldOfCoordinatesCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1))) (unitVariation j)
        ∂multivariateGaussian 0 G := by
  have hC := growthConst_nonneg F Cg k hgrow
  have hd1 : Differentiable ℝ (fderiv ℝ F) := (contDiff_one_fderiv F hF).differentiable (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ F)) := (contDiff_one_fderiv F hF).continuous_fderiv (by norm_num)
  have hpt : ∀ ζ, HasFDerivAt (rotatedPoint θ η) (Real.sin θ • fieldOfCoordinatesCLM) ζ := fun ζ => by
    unfold rotatedPoint
    exact (fieldOfCoordinatesCLM.hasFDerivAt.const_smul (Real.sin θ)).const_add _
  have hΦ : ∀ ζ, HasFDerivAt (fun ζ => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j))
      ((ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).comp
        ((fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)).comp (Real.sin θ • fieldOfCoordinatesCLM))) ζ := fun ζ =>
    (ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).hasFDerivAt.comp ζ ((hd1 _).hasFDerivAt.comp ζ (hpt ζ))
  have hfd : fderiv ℝ (fun ζ => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j)) = fun ζ =>
      (ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).comp
        ((fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)).comp (Real.sin θ • fieldOfCoordinatesCLM)) :=
    funext fun ζ => (hΦ ζ).fderiv
  have cpt : Continuous (rotatedPoint θ η) := continuous_iff_continuousAt.2 fun ζ => (hpt ζ).continuousAt
  set c₀ := ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖ with hc₀
  set U := ‖unitVariation j‖ with hU
  have hsz : ∀ ζ, (1 + ‖rotatedPoint θ η ζ‖) ^ k ≤ ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k := fun ζ => by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have := one_add_norm_rotatedPoint θ η ζ
    calc _ ≤ _ := this
      _ = _ := by ring
  have hst := stein_multivariateGaussian G hG (fun ζ => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j))
    (fun ζ => (hΦ ζ).differentiableAt) ?_
    (Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (U + (1 + c₀) * U)) k ?_ ?_ j
  · rw [hst, hfd, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  · rw [hfd]
    exact ((continuous_const).clm_comp ((hc2.comp cpt).clm_comp continuous_const))
  · intro ζ
    have hUn : 0 ≤ U := norm_nonneg _
    calc |fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j)| ≤ ‖fderiv ℝ F (rotatedPoint θ η ζ)‖ * U :=
          (fderiv ℝ F _).le_opNorm _
      _ ≤ (Cg * (((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k)) * U := by
          gcongr
          exact le_trans (norm_fderiv_le_growth F Cg k hgrow _) (mul_le_mul_of_nonneg_left (hsz ζ) hC)
      _ ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (U + (1 + c₀) * U) * (1 + ‖ζ‖) ^ k := by
          have : U ≤ U + (1 + c₀) * U := by
            have : 0 ≤ (1 + c₀) * U := by positivity
            linarith
          have h2 : 0 ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k := by positivity
          calc _ = Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k * U := by ring
            _ ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k * (U + (1 + c₀) * U) := by gcongr
            _ = _ := by ring
  · intro ζ
    rw [hfd]
    have hUn : 0 ≤ U := norm_nonneg _
    have hK : 0 ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (U + (1 + c₀) * U) * (1 + ‖ζ‖) ^ k := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun v => ?_
    have e1 : ((ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).comp
        ((fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)).comp (Real.sin θ • fieldOfCoordinatesCLM))) v =
        fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ) (Real.sin θ • fieldOfCoordinatesCLM v) (unitVariation j) := rfl
    rw [e1, Real.norm_eq_abs]
    have h1 : ‖Real.sin θ • fieldOfCoordinatesCLM v‖ ≤ c₀ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)) (fieldOfCoordinatesCLM.le_opNorm v)
    have h2 : ‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)‖ ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k := by
      refine le_trans (norm_fderiv_fderiv_le_growth F Cg k hgrow _) ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsz ζ) hC
    calc |fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ) (Real.sin θ • fieldOfCoordinatesCLM v) (unitVariation j)|
        ≤ ‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ) (Real.sin θ • fieldOfCoordinatesCLM v)‖ * U := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)‖ * ‖Real.sin θ • fieldOfCoordinatesCLM v‖ * U := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k) * (c₀ * ‖v‖) * U := by gcongr
      _ ≤ (Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (U + (1 + c₀) * U) * (1 + ‖ζ‖) ^ k) * ‖v‖ := by
          have h3 : c₀ * U ≤ U + (1 + c₀) * U := by nlinarith
          calc _ = Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k * ‖v‖ * (c₀ * U) := by ring
            _ ≤ Cg * ((1 + c₀) * (1 + ‖η‖)) ^ k * (1 + ‖ζ‖) ^ k * ‖v‖ * (U + (1 + c₀) * U) := by gcongr
            _ = _ := by ring
include hF in
private theorem byParts_along_rotation (hB : cutoffIntegrationByPartsStatement)
    (hP : normalizedBallLawIsProbabilityStatement) (ρ : ℝ) (p : ℝ → ℝ)
    (Ψ : BondField ι → ℝ) (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hΨ : ContDiff ℝ 1 Ψ) (θ : ℝ)
    (ζ : EuclideanSpace ℝ (Fin 3 × ι)) (u : BondField ι) (j : Fin 3 × ι) :
    Real.cos θ * ∫ η, fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ) u (unitVariation j) ∂normalizedBallLaw (cutoffFactor ρ p) Ψ =
      ∫ η, fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j) * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b))
        ∂normalizedBallLaw (cutoffFactor ρ p) Ψ := by
  obtain ⟨-, hmean, -⟩ := hP ι ρ p Ψ hρ hcut hΨ.continuous
  have hd1 : Differentiable ℝ (fderiv ℝ F) := (contDiff_one_fderiv F hF).differentiable (by norm_num)
  have hptc : ∀ η, HasFDerivAt (fun η => rotatedPoint θ η ζ)
      (Real.cos θ • ContinuousLinearMap.id ℝ (BondField ι)) η := fun η => by
    unfold rotatedPoint
    exact ((hasFDerivAt_id η).const_smul (Real.cos θ)).add_const _
  have hg : ContDiff ℝ 1 (fun η => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j)) := by
    have c1 : ContDiff ℝ 1 (fun η : BondField ι => rotatedPoint θ η ζ) := by
      unfold rotatedPoint
      exact (contDiff_const_smul _).add contDiff_const
    exact ((contDiff_one_fderiv F hF).comp c1).clm_apply contDiff_const
  have hfg : ∀ η, fderiv ℝ (fun η => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j)) η u =
      Real.cos θ * fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ) u (unitVariation j) := fun η => by
    have h1 : HasFDerivAt (fun η => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j))
        ((ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).comp ((fderiv ℝ (fderiv ℝ F) (rotatedPoint θ η ζ)).comp
          (Real.cos θ • ContinuousLinearMap.id ℝ (BondField ι)))) η :=
      (ContinuousLinearMap.apply ℝ ℝ (unitVariation j)).hasFDerivAt.comp η ((hd1 _).hasFDerivAt.comp η (hptc η))
    rw [h1.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  have hbp := hB ι ρ p Ψ (fun η => fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j)) u hρ hcut (hΨ) hg
  rw [hmean, hmean]
  unfold ballExpectation
  rw [← mul_div_assoc]
  congr 1
  have e : ∀ η, (fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j) *
      (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b))) * ballDensity (cutoffFactor ρ p) Ψ η =
      fderiv ℝ F (rotatedPoint θ η ζ) (unitVariation j) * (fderiv ℝ Ψ η u + ∑ b, cutoffRadialDeriv p (η b) (u b)) *
        ballDensity (cutoffFactor ρ p) Ψ η := fun η => rfl
  rw [← hbp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [hfg]
  ring
section ProductMeasure
variable (μ : Measure (BondField ι)) [IsProbabilityMeasure μ] (R : ℝ) (hμ : ∀ᵐ η ∂μ, ‖η‖ ≤ R)
  (γ : Measure (EuclideanSpace ℝ (Fin 3 × ι))) [IsGaussian γ]
include hμ in
private theorem integrable_productWeight (m : ℕ) :
    Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => (1 + ‖z.1‖) ^ m * (1 + ‖z.2‖) ^ m) (μ.prod γ) := by
  have h1 : Integrable (fun η : BondField ι => (1 + ‖η‖) ^ m) μ := by
    refine Integrable.of_bound ((continuous_const.add continuous_norm).pow m).aestronglyMeasurable ((1 + |R|) ^ m) ?_
    filter_upwards [hμ] with η hη
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith [le_abs_self R]) m
  exact Integrable.mul_prod h1 (integrable_one_add_norm_pow γ m)
include hμ in
private theorem integrable_of_productWeight_bound (h : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) → ℝ)
    (hc : AEStronglyMeasurable h (μ.prod γ))
    (C : ℝ) (m : ℕ) (hb : ∀ z, |h z| ≤ C * ((1 + ‖z.1‖) ^ m * (1 + ‖z.2‖) ^ m)) : Integrable h (μ.prod γ) :=
  ((integrable_productWeight μ R hμ γ m).const_mul C).mono' hc (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hb z)
private def rotationDirection (θ : ℝ) (η : BondField ι) (ζ : EuclideanSpace ℝ (Fin 3 × ι)) : BondField ι :=
  (-Real.sin θ) • η + Real.cos θ • fieldOfCoordinatesCLM ζ
private theorem one_add_norm_rotationDirection (θ : ℝ) (η : BondField ι) (ζ : EuclideanSpace ℝ (Fin 3 × ι)) :
    1 + ‖rotationDirection θ η ζ‖ ≤
      (1 + ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖) * ((1 + ‖η‖) * (1 + ‖ζ‖)) := by
  have h1 : ‖rotationDirection θ η ζ‖ ≤
      ‖η‖ + ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖ * ‖ζ‖ := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)
    · rw [norm_smul, Real.norm_eq_abs]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)) (fieldOfCoordinatesCLM.le_opNorm ζ)
  have a := norm_nonneg η
  have b := norm_nonneg ζ
  have c := norm_nonneg (fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)
  nlinarith [mul_nonneg a b, mul_nonneg c a, mul_nonneg c b, mul_nonneg (mul_nonneg c a) b]
private theorem continuous_rotatedPoint (θ : ℝ) :
    Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => rotatedPoint θ z.1 z.2 :=
  (continuous_fst.const_smul (Real.cos θ)).add ((fieldOfCoordinatesCLM.continuous.comp continuous_snd).const_smul (Real.sin θ))
private theorem continuous_rotationDirection (θ : ℝ) :
    Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => rotationDirection θ z.1 z.2 :=
  (continuous_fst.const_smul (-Real.sin θ)).add
    ((fieldOfCoordinatesCLM.continuous.comp continuous_snd).const_smul (Real.cos θ))
private theorem one_add_norm_rotatedPoint_pow_le (θ : ℝ) (z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι)) (m : ℕ) :
    (1 + ‖rotatedPoint θ z.1 z.2‖) ^ m ≤
      (1 + ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖) ^ m *
        ((1 + ‖z.1‖) ^ m * (1 + ‖z.2‖) ^ m) := by
  rw [← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_rotatedPoint θ z.1 z.2) m
section Rotation
include hF hgrow hμ in
private theorem hasDerivAt_integral_rotatedPoint (θ₀ : ℝ) :
    HasDerivAt (fun θ => ∫ z, F (rotatedPoint θ z.1 z.2) ∂(μ.prod γ))
      (∫ z, fderiv ℝ F (rotatedPoint θ₀ z.1 z.2) (rotationDirection θ₀ z.1 z.2) ∂(μ.prod γ)) θ₀ := by
  have hC := growthConst_nonneg F Cg k hgrow
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hF.continuous
  have hc1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  set c₀ := ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖ with hc₀
  have hb : ∀ (θ : ℝ) (z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι)),
      ‖fderiv ℝ F (rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2)‖ ≤
        (Cg * (1 + c₀) ^ (k + 1)) * ((1 + ‖z.1‖) ^ (k + 1) * (1 + ‖z.2‖) ^ (k + 1)) := fun θ z => by
    have a1 : ‖rotationDirection θ z.1 z.2‖ ≤ (1 + c₀) * ((1 + ‖z.1‖) * (1 + ‖z.2‖)) := by
      have := one_add_norm_rotationDirection θ z.1 z.2
      linarith
    have a2 : ‖fderiv ℝ F (rotatedPoint θ z.1 z.2)‖ ≤ Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) :=
      le_trans (norm_fderiv_le_growth F Cg k hgrow _)
        (mul_le_mul_of_nonneg_left (one_add_norm_rotatedPoint_pow_le θ z k) hC)
    calc _ ≤ ‖fderiv ℝ F (rotatedPoint θ z.1 z.2)‖ * ‖rotationDirection θ z.1 z.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k))) * ((1 + c₀) * ((1 + ‖z.1‖) * (1 + ‖z.2‖))) := by
          gcongr
      _ = _ := by ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun θ (z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι)) => F (rotatedPoint θ z.1 z.2))
    (F' := fun θ (z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι)) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2))
    (bound := fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      (Cg * (1 + c₀) ^ (k + 1)) * ((1 + ‖z.1‖) ^ (k + 1) * (1 + ‖z.2‖) ^ (k + 1)))
    (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun θ => (hFc.comp (continuous_rotatedPoint θ)).aestronglyMeasurable
  · refine integrable_of_productWeight_bound μ R hμ γ _ (hFc.comp (continuous_rotatedPoint θ₀)).aestronglyMeasurable
      (Cg * (1 + c₀) ^ k) k fun z => ?_
    refine le_trans (abs_le_growth F Cg k hgrow _) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (one_add_norm_rotatedPoint_pow_le θ₀ z k) hC
  · exact ((hc1.comp (continuous_rotatedPoint θ₀)).clm_apply (continuous_rotationDirection θ₀)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z θ _ => hb θ z
  · exact (integrable_productWeight μ R hμ γ (k + 1)).const_mul _
  · refine Filter.Eventually.of_forall fun z θ _ => ?_
    have h1 : HasDerivAt (fun θ => rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2) θ := by
      unfold rotatedPoint rotationDirection
      exact ((Real.hasDerivAt_cos θ).smul_const z.1).add ((Real.hasDerivAt_sin θ).smul_const (fieldOfCoordinatesCLM z.2))
    exact ((hFd _).hasFDerivAt.comp_hasDerivAt θ h1)
private theorem measurable_cutoffRadialDeriv (p : ℝ → ℝ) (b : ι) (v : BondVector) :
    Measurable fun η : BondField ι => cutoffRadialDeriv p (η b) v := by apply _root_.YangMills.Construction.LinearResponse.measurable_cutoffRadialDeriv <;> assumption
private theorem measurable_driftCoord (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ)
    (hΨ : ContDiff ℝ 1 Ψ) (j : Fin 3 × ι) : Measurable fun η => driftCoord G p Ψ η j := by
  unfold driftCoord
  refine Measurable.sub (Finset.measurable_sum _ fun i _ => Measurable.const_mul ?_ _) ?_
  · unfold gradientCoord
    exact (((hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable).add
      (measurable_cutoffRadialDeriv p _ _)
  · have : Continuous fun η : BondField ι => (η j.2) j.1 := by fun_prop
    exact this.measurable
include hF hgrow hμ in
private theorem deriv_integral_rotatedPoint_eq (hB : cutoffIntegrationByPartsStatement)
    (hP : normalizedBallLawIsProbabilityStatement) (ρ : ℝ) (p : ℝ → ℝ)
    (Ψ : BondField ι → ℝ) (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hΨ : ContDiff ℝ 1 Ψ)
    (hμe : μ = normalizedBallLaw (cutoffFactor ρ p) Ψ)
    (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (hG : G.PosSemidef) (hγ : γ = multivariateGaussian 0 G) (θ : ℝ)
    (hd : ∀ j, MemLp (fun η => driftCoord G p Ψ η j) 2 μ) :
    ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2) ∂(μ.prod γ) =
      Real.sin θ * ∑ j, ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * driftCoord G p Ψ z.1 j ∂(μ.prod γ) := by
  subst hμe hγ
  have hC := growthConst_nonneg F Cg k hgrow
  have hc1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ F)) := (contDiff_one_fderiv F hF).continuous_fderiv (by norm_num)
  set c₀ := ‖(fieldOfCoordinatesCLM : EuclideanSpace ℝ (Fin 3 × ι) →L[ℝ] BondField ι)‖ with hc₀
  have hg : ∀ (j : Fin 3 × ι) (z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι)),
      |fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j)| ≤
        (Cg * (1 + c₀) ^ k * ‖unitVariation j‖) * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k) := fun j z => by
    have a2 : ‖fderiv ℝ F (rotatedPoint θ z.1 z.2)‖ ≤ Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) :=
      le_trans (norm_fderiv_le_growth F Cg k hgrow _)
        (mul_le_mul_of_nonneg_left (one_add_norm_rotatedPoint_pow_le θ z k) hC)
    calc _ ≤ ‖fderiv ℝ F (rotatedPoint θ z.1 z.2)‖ * ‖unitVariation j‖ := (fderiv ℝ F _).le_opNorm _
      _ ≤ (Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k))) * ‖unitVariation j‖ := by gcongr
      _ = _ := by ring
  have cg : ∀ j : Fin 3 × ι, Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) :=
    fun j => (hc1.comp (continuous_rotatedPoint θ)).clm_apply continuous_const
  have hgL : ∀ j : Fin 3 × ι, MemLp (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j)) 2
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    refine (memLp_two_iff_integrable_sq (cg j).aestronglyMeasurable).2 ?_
    refine integrable_of_productWeight_bound _ R hμ _ _ ((cg j).pow 2).aestronglyMeasurable
      ((Cg * (1 + c₀) ^ k * ‖unitVariation j‖) ^ 2) (2 * k) fun z => ?_
    rw [abs_pow, pow_mul', pow_mul', ← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hg j z) 2
  have hdL : ∀ j : Fin 3 × ι, MemLp (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => driftCoord G p Ψ z.1 j) 2
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j =>
    (hd j).comp_measurePreserving (measurePreserving_fst)
  have I4 : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * driftCoord G p Ψ z.1 j)
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) :=
    fun j => (hgL j).integrable_mul (hdL j)
  have I2 : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * z.1 j.2 j.1)
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    have c1 : Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => z.1 j.2 j.1 := by fun_prop
    refine integrable_of_productWeight_bound _ R hμ _ _ ((cg j).mul c1).aestronglyMeasurable
      (Cg * (1 + c₀) ^ k * ‖unitVariation j‖) (k + 1) fun z => ?_
    rw [abs_mul]
    have a1 : |z.1 j.2 j.1| ≤ 1 + ‖z.1‖ := by
      have h1 : |z.1 j.2 j.1| ≤ ‖z.1 j.2‖ := PiLp.norm_apply_le (z.1 j.2) j.1
      have h2 : ‖z.1 j.2‖ ≤ ‖z.1‖ := norm_le_pi_norm z.1 j.2
      linarith
    have hb1 : 1 ≤ 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
    calc _ ≤ ((Cg * (1 + c₀) ^ k * ‖unitVariation j‖) * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) * (1 + ‖z.1‖) := by
          gcongr
          exact hg j z
      _ ≤ ((Cg * (1 + c₀) ^ k * ‖unitVariation j‖) * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) * (1 + ‖z.1‖) * (1 + ‖z.2‖) :=
          le_mul_of_one_le_right (by positivity) hb1
      _ = _ := by ring
  have I1 : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      z.2 j * fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j))
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    have c1 : Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => z.2 j := by fun_prop
    refine integrable_of_productWeight_bound _ R hμ _ _ (c1.mul (cg j)).aestronglyMeasurable
      (Cg * (1 + c₀) ^ k * ‖unitVariation j‖) (k + 1) fun z => ?_
    rw [abs_mul]
    have a1 : |z.2 j| ≤ 1 + ‖z.2‖ := by
      have h1 : |z.2 j| ≤ ‖z.2‖ := PiLp.norm_apply_le z.2 j
      linarith
    have hb1 : 1 ≤ 1 + ‖z.1‖ := by linarith [norm_nonneg z.1]
    calc _ ≤ (1 + ‖z.2‖) * ((Cg * (1 + c₀) ^ k * ‖unitVariation j‖) * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) := by
          gcongr
          exact hg j z
      _ ≤ (1 + ‖z.2‖) * ((Cg * (1 + c₀) ^ k * ‖unitVariation j‖) * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) * (1 + ‖z.1‖) :=
          le_mul_of_one_le_right (by positivity) hb1
      _ = _ := by ring
  set u : Fin 3 × ι → BondField ι := fun j =>
    fieldOfCoordinatesCLM (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1)) with hu
  have I3 : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2) (u j) (unitVariation j))
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    have c1 : Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
        fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2) (u j) (unitVariation j) :=
      ((hc2.comp (continuous_rotatedPoint θ)).clm_apply continuous_const).clm_apply continuous_const
    refine integrable_of_productWeight_bound _ R hμ _ _ c1.aestronglyMeasurable
      (Cg * (1 + c₀) ^ k * ‖u j‖ * ‖unitVariation j‖) k fun z => ?_
    have a2 : ‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2)‖ ≤
        Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k)) :=
      le_trans (norm_fderiv_fderiv_le_growth F Cg k hgrow _)
        (mul_le_mul_of_nonneg_left (one_add_norm_rotatedPoint_pow_le θ z k) hC)
    rw [← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2) (u j)‖ * ‖unitVariation j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2)‖ * ‖u j‖) * ‖unitVariation j‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((Cg * ((1 + c₀) ^ k * ((1 + ‖z.1‖) ^ k * (1 + ‖z.2‖) ^ k))) * ‖u j‖) * ‖unitVariation j‖ := by gcongr
      _ = _ := by ring
  have hT : ∀ (j : Fin 3 × ι) (η : BondField ι),
      fderiv ℝ Ψ η (u j) + ∑ b, cutoffRadialDeriv p (η b) (u j b) = driftCoord G p Ψ η j + η j.2 j.1 := fun j η => by
    rw [fderiv_add_cutoff_eq_sum_gradientCoord]
    have hco : ∀ i : Fin 3 × ι, (u j) i.2 i.1 = G j i := fun i => by
      have hsym : G i j = G j i := by
        have := hG.isHermitian.apply i j
        simpa using this.symm
      rw [← hsym]
      simp only [hu, fieldOfCoordinatesCLM_apply, fieldOfCoordinates]
      show (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1)) i = G i j
      have e : (Matrix.toEuclideanCLM (𝕜 := ℝ) G (EuclideanSpace.single j 1)).ofLp =
          G.mulVec (EuclideanSpace.single j (1 : ℝ)).ofLp :=
        Matrix.ofLp_toEuclideanCLM G _
      rw [e]
      simp
    unfold driftCoord
    simp only [hco]
    ring
  have I5 : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) *
        (fderiv ℝ Ψ z.1 (u j) + ∑ b, cutoffRadialDeriv p (z.1 b) (u j b)))
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    refine ((I4 j).add (I2 j)).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, hT]
    ring
  have step1 : ∀ j : Fin 3 × ι, ∫ z, z.2 j * fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j)
      ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) =
      Real.sin θ * ∫ z, fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2) (u j) (unitVariation j)
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    rw [integral_prod _ (I1 j), integral_prod _ (I3 j), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    exact stein_along_rotation F hF Cg k hgrow G hG θ η j
  have step2 : ∀ j : Fin 3 × ι, Real.cos θ * ∫ z, fderiv ℝ (fderiv ℝ F) (rotatedPoint θ z.1 z.2) (u j) (unitVariation j)
      ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) =
      ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) *
        (fderiv ℝ Ψ z.1 (u j) + ∑ b, cutoffRadialDeriv p (z.1 b) (u j b))
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    rw [integral_prod_symm _ (I3 j), integral_prod_symm _ (I5 j), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    exact byParts_along_rotation F hF hB hP ρ p Ψ hρ hcut hΨ θ ζ (u j) j
  have step3 : ∀ j : Fin 3 × ι, ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) *
      (fderiv ℝ Ψ z.1 (u j) + ∑ b, cutoffRadialDeriv p (z.1 b) (u j b))
      ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) =
      (∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * driftCoord G p Ψ z.1 j
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) +
        ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * z.1 j.2 j.1
          ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j => by
    rw [← integral_add (I4 j) (I2 j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hT]
    ring
  have hexp : ∀ z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι),
      fderiv ℝ F (rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2) =
      ∑ j : Fin 3 × ι, ((-Real.sin θ) * (fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * z.1 j.2 j.1) +
        Real.cos θ * (z.2 j * fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j))) := fun z => by
    rw [clm_apply_eq_sum (fderiv ℝ F _) (rotationDirection θ z.1 z.2)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (rotationDirection θ z.1 z.2) j.2 j.1 = (-Real.sin θ) * z.1 j.2 j.1 + Real.cos θ * z.2 j := by
      simp [rotationDirection, fieldOfCoordinatesCLM_apply, fieldOfCoordinates]
    rw [e1]
    ring
  simp_rw [hexp]
  have J : ∀ j : Fin 3 × ι, Integrable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
      (-Real.sin θ) * (fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * z.1 j.2 j.1) +
        Real.cos θ * (z.2 j * fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j)))
      ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) := fun j =>
    ((I2 j).const_mul _).add ((I1 j).const_mul _)
  rw [integral_finset_sum _ (fun j _ => J j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add ((I2 j).const_mul _) ((I1 j).const_mul _), integral_const_mul, integral_const_mul, step1 j]
  have h2 := step2 j
  have h3 := step3 j
  linear_combination Real.sin θ * h2 + Real.sin θ * h3
end Rotation
end ProductMeasure
end BondFields
private theorem eLpNorm_comp_fst {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (q : ENNReal) :
    eLpNorm (fun z : X × Y => f z.1) q (μ.prod ν) = eLpNorm f q μ :=
  eLpNorm_comp_measurePreserving hf measurePreserving_fst
private theorem enorm_integral_mul_le {X : Type} [MeasurableSpace X] (P : Measure X) (g d : X → ℝ)
    (hg : AEStronglyMeasurable g P) (hd : AEStronglyMeasurable d P) :
    ‖∫ z, g z * d z ∂P‖ₑ ≤ eLpNorm g 2 P * eLpNorm d 2 P := by
  have h3 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := P) hd hg
  refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
  refine le_trans ?_ h3
  rw [eLpNorm_one_eq_lintegral_enorm]
  rfl
set_option maxHeartbeats 1000000 in
theorem gaussianComparison (hB : cutoffIntegrationByPartsStatement) (hP : normalizedBallLawIsProbabilityStatement) :
    gaussianComparisonStatement := by
  intro ι _ _ ρ p Ψ F G Cg A k c hρ hcut hΨ hG hF hA hgrow hdrift hθ
  obtain ⟨hprob, -, -, hballs, -⟩ := hP ι ρ p Ψ hρ hcut hΨ.continuous
  haveI := hprob
  have hμR : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, ‖η‖ ≤ ρ :=
    hballs.mono fun η h => (pi_norm_le_iff_of_nonneg hρ.le).2 fun b => (h b).le
  have hd : ∀ j, MemLp (fun η => driftCoord G p Ψ η j) 2 (normalizedBallLaw (cutoffFactor ρ p) Ψ) := fun j =>
    ⟨(measurable_driftCoord G p Ψ hΨ j).aestronglyMeasurable, lt_of_le_of_lt (hdrift j) ENNReal.ofReal_lt_top⟩
  have hFc : Continuous F := hF.continuous
  have hc1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hD := hasDerivAt_integral_rotatedPoint F hF Cg k hgrow (normalizedBallLaw (cutoffFactor ρ p) Ψ) ρ hμR
    (multivariateGaussian 0 G)
  have hform := fun θ => deriv_integral_rotatedPoint_eq F hF Cg k hgrow (normalizedBallLaw (cutoffFactor ρ p) Ψ) ρ hμR
    (multivariateGaussian 0 G) hB hP ρ p Ψ hρ hcut hΨ rfl G hG rfl θ hd
  have hS : ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 →
      |∑ j, ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) * driftCoord G p Ψ z.1 j
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))| ≤ A := fun θ h0 h1 => by
    rw [← ENNReal.ofReal_le_ofReal_iff hA]
    refine le_trans ?_ (hθ θ h0 h1)
    rw [← Real.enorm_eq_ofReal_abs]
    refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    have cg : Continuous fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) =>
        fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) :=
      (hc1.comp (continuous_rotatedPoint θ)).clm_apply continuous_const
    have md : AEStronglyMeasurable (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => driftCoord G p Ψ z.1 j)
        ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) :=
      ((measurable_driftCoord G p Ψ hΨ j).comp measurable_fst).aestronglyMeasurable
    have h2 : eLpNorm (fun z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι) => driftCoord G p Ψ z.1 j) 2
        ((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) ≤ ENNReal.ofReal (c j) := by
      refine le_trans (le_of_eq ?_) (hdrift j)
      exact eLpNorm_comp_fst _ _ _ (hd j).1 2
    refine le_trans (enorm_integral_mul_le _ _ _ cg.aestronglyMeasurable md) ?_
    rw [mul_comm]
    exact mul_le_mul' h2 le_rfl
  have hmono : ∀ s : ℝ, |s| = 1 →
      s * (∫ z, F (rotatedPoint (Real.pi / 2) z.1 z.2)
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) ≤
      s * (∫ z, F (rotatedPoint 0 z.1 z.2)
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) + A := fun s hs => by
    have hanti : AntitoneOn (fun θ => s * (∫ z, F (rotatedPoint θ z.1 z.2)
        ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) + A * Real.cos θ)
        (Set.Icc 0 (Real.pi / 2)) := by
      have hder : ∀ θ, HasDerivAt (fun θ => s * (∫ z, F (rotatedPoint θ z.1 z.2)
          ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) + A * Real.cos θ)
          (s * (∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (rotationDirection θ z.1 z.2)
            ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))) + A * (-Real.sin θ)) θ :=
        fun θ => ((hD θ).const_mul s).add ((Real.hasDerivAt_cos θ).const_mul A)
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun θ _ => (hder θ).continuousAt.continuousWithinAt)
        (fun θ _ => (hder θ).differentiableAt.differentiableWithinAt) fun θ hθ' => ?_
      rw [(hder θ).deriv, hform θ]
      rw [interior_Icc] at hθ'
      have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1.le (by linarith [hθ'.2, Real.pi_pos])
      have h1 := hS θ hθ'.1.le hθ'.2.le
      have h2 := le_trans (le_abs_self _) (show |s * ∑ j, ∫ z, fderiv ℝ F (rotatedPoint θ z.1 z.2) (unitVariation j) *
        driftCoord G p Ψ z.1 j ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G))| ≤ A by
          rw [abs_mul, hs, one_mul]; exact h1)
      nlinarith
    have h := hanti (Set.left_mem_Icc.2 (by positivity)) (Set.right_mem_Icc.2 (by positivity)) (by positivity)
    simp only [Real.cos_zero, Real.cos_pi_div_two, mul_zero, add_zero, mul_one] at h
    exact h
  have e0 : ∫ z, F (rotatedPoint 0 z.1 z.2) ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) =
      ∫ η, F η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ := by
    have e : ∀ z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι), rotatedPoint 0 z.1 z.2 = z.1 := fun z => by
      simp [rotatedPoint]
    simp only [e]
    rw [integral_fun_fst]
    simp
  have e1 : ∫ z, F (rotatedPoint (Real.pi / 2) z.1 z.2)
      ∂((normalizedBallLaw (cutoffFactor ρ p) Ψ).prod (multivariateGaussian 0 G)) =
      ∫ ζ, F (fieldOfCoordinates ζ) ∂multivariateGaussian 0 G := by
    have e : ∀ z : BondField ι × EuclideanSpace ℝ (Fin 3 × ι),
        rotatedPoint (Real.pi / 2) z.1 z.2 = fieldOfCoordinates z.2 := fun z => by
      simp [rotatedPoint, fieldOfCoordinatesCLM_apply]
    simp only [e]
    rw [integral_fun_snd (f := fun ζ => F (fieldOfCoordinates ζ))]
    simp
  rw [e0, e1] at hmono
  have h1 := hmono 1 (by simp)
  have h2 := hmono (-1) (by simp)
  rw [abs_le]
  constructor <;> linarith
end YangMills.Construction.MomentMethod
end
