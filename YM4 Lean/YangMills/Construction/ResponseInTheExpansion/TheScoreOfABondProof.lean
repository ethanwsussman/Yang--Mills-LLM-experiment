import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorel
import YangMills.Construction.ResponseInTheExpansion.ProductsOfScoresAtAStepProof
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts BlockAverages
namespace BondScore
theorem hasDerivAt_integral_exp_mul (φ : UnitQuaternion → ℝ) (hφ : Continuous φ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ g, Real.exp (t * φ g) ∂haarUnit)
      (∫ g, φ g * Real.exp (y * φ g) ∂haarUnit) y := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hB' : ∀ g, |φ g| ≤ B := fun g => by simpa using hB g (Set.mem_univ g)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 1)
  have hexpc : ∀ t : ℝ, Continuous fun g => Real.exp (t * φ g) := fun t =>
    Real.continuous_exp.comp (continuous_const.mul hφ)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := haarUnit) (𝕜 := ℝ)
    (F := fun t g => Real.exp (t * φ g)) (F' := fun t g => φ g * Real.exp (t * φ g))
    (bound := fun _ => B * Real.exp ((|y| + 1) * B)) (s := Metric.ball y 1) (x₀ := y)
    (Metric.ball_mem_nhds y one_pos)
    (Filter.Eventually.of_forall fun t => (hexpc t).aestronglyMeasurable)
    ((hexpc y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hφ.mul (hexpc y)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g t ht => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun g t _ => ?_)).2
  · have ht' : |t| ≤ |y| + 1 := by
      have h1 : |t - y| < 1 := by simpa [Real.dist_eq] using ht
      have h2 := abs_sub_abs_le_abs_sub t y
      linarith
    have hle : t * φ g ≤ (|y| + 1) * B := by
      calc t * φ g ≤ |t * φ g| := le_abs_self _
        _ = |t| * |φ g| := abs_mul _ _
        _ ≤ (|y| + 1) * B := mul_le_mul ht' (hB' g) (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hB' g) (Real.exp_le_exp.mpr hle) (Real.exp_pos _).le hB0
  · have h := ((hasDerivAt_id t).mul_const (φ g)).exp
    simpa [mul_comm] using h
theorem continuous_re_unitQuaternion :
    Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
theorem hasDerivAt_partitionFn (s : ℝ) : HasDerivAt partitionFn (deriv partitionFn s) s := by
  have h := hasDerivAt_integral_exp_mul (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re)
    continuous_re_unitQuaternion s
  exact (HasDerivAt.differentiableAt (f := partitionFn) h).hasDerivAt
theorem partitionFn_pos (hK : BondKernelProperties) (s : ℝ) : 0 < partitionFn s := by
  rcases le_total 0 s with hs | hs
  · exact lt_of_lt_of_le one_pos (hK.1 s hs).1
  · unfold partitionFn
    exact integral_exp_pos ((Real.continuous_exp.comp
      (continuous_const.mul continuous_re_unitQuaternion)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
theorem deriv_logPartitionGap (hK : BondKernelProperties) (s : ℝ) :
    deriv logPartitionGap s = 1 - deriv partitionFn s / partitionFn s := by
  have h : HasDerivAt logPartitionGap (1 - deriv partitionFn s / partitionFn s) s :=
    (hasDerivAt_id s).sub ((hasDerivAt_partitionFn s).log (partitionFn_pos hK s).ne')
  exact h.deriv
variable {n : ℕ} [NeZero n]
theorem integral_kernelOfElement (hK : BondKernelProperties) (ℓ : StepParameters) (x : ℝ)
    (w : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : ∫ g, kernelOfElement ℓ x w b c g ∂haarUnit = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ScoreProducts.integral_kernelOfElement_eq_one <;> assumption
theorem meanNorm_eq_norm_bondMean (ℓ : StepParameters) (W : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    meanNorm ℓ W b c = ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c‖ := rfl
theorem integral_re_mul_exp (hK : BondKernelProperties) (ℓ : StepParameters) (ha : ℓ.coupling ≠ 0)
    (w : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (c : TorusBond n) (y : ℝ) :
    ∫ g : UnitQuaternion, (bondMean ℓ w b c * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re *
        Real.exp (y * (bondMean ℓ w b c * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ∂haarUnit =
      ‖bondMean ℓ w b c‖ * deriv partitionFn (y * ‖bondMean ℓ w b c‖) := by
  set q := bondMean ℓ w b c with hq
  have hφ : Continuous fun g : UnitQuaternion => (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
    continuous_re_mul_inv q
  have hE : (fun t : ℝ => ∫ g : UnitQuaternion,
      Real.exp (t * (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ∂haarUnit) =
      fun t => partitionFn (t * ‖q‖) := by
    funext t
    have h := integral_kernelOfElement hK ℓ (t / ℓ.coupling) w b c
    simp only [kernelOfElement] at h
    rw [integral_div] at h
    have ht : ℓ.coupling * (t / ℓ.coupling) = t := by field_simp
    rw [ht, ← hq] at h
    exact (div_eq_one_iff_eq (partitionFn_pos hK _).ne').mp h
  have h1 := hasDerivAt_integral_exp_mul _ hφ y
  rw [hE] at h1
  have h2 : HasDerivAt (fun t : ℝ => partitionFn (t * ‖q‖)) (deriv partitionFn (y * ‖q‖) * ‖q‖) y :=
    HasDerivAt.comp (h₂ := partitionFn) y (hasDerivAt_partitionFn (y * ‖q‖)) (hasDerivAt_mul_const ‖q‖)
  rw [h1.unique h2, mul_comm]
theorem fitConditionalMean_eq (hK : BondKernelProperties) (ℓ : StepParameters) (ha : ℓ.coupling ≠ 0) (x : ℝ)
    (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    fitConditionalMean ℓ x W b c =
      meanNorm ℓ W b c * deriv logPartitionGap (ℓ.coupling * x * meanNorm ℓ W b c) := by
  set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
  set q := bondMean ℓ w b c with hq
  have hr : meanNorm ℓ W b c = ‖q‖ := rfl
  rw [hr, deriv_logPartitionGap hK]
  have h1 : fitConditionalMean ℓ x W b c = ∫ g : UnitQuaternion, (‖q‖ * kernelOfElement ℓ x w b c g -
      (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re *
        Real.exp (ℓ.coupling * x * (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
        partitionFn (ℓ.coupling * x * ‖q‖)) ∂haarUnit := by
    unfold fitConditionalMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show bondFit ℓ W _ b c * bondKernelAt ℓ x W _ b c = _
    rw [bondFit_eq_fitOfElement, bondKernelAt_eq_kernelOfElement, fieldAtBond_apply_self]
    simp only [fitOfElement, kernelOfElement, ← hq, ← hw]
    ring
  have hk : Continuous (kernelOfElement ℓ x w b c) := continuous_kernelOfElement ℓ x w b c
  have hi1 : Integrable (fun g : UnitQuaternion => ‖q‖ * kernelOfElement ℓ x w b c g) haarUnit :=
    (continuous_const.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun g : UnitQuaternion => (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re *
      Real.exp (ℓ.coupling * x * (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
        partitionFn (ℓ.coupling * x * ‖q‖)) haarUnit :=
    (((continuous_re_mul_inv q).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_re_mul_inv q)))).div_const _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [h1, integral_sub hi1 hi2, integral_const_mul, integral_kernelOfElement hK, integral_div,
    integral_re_mul_exp hK ℓ ha w b c (ℓ.coupling * x), ← hq]
  field_simp
local instance instMeasurableSpaceQuaternionBorel : MeasurableSpace ℍ[ℝ] := borel _
local instance instBorelSpaceQuaternion : BorelSpace ℍ[ℝ] := ⟨rfl⟩
instance instSecondCountableTopologyUnitQuaternion : SecondCountableTopology UnitQuaternion :=
  TopologicalSpace.Subtype.secondCountableTopology _
theorem measurable_bondMean (hB : BondKernelBorel) (ℓ : StepParameters) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) :
    Measurable fun W : TorusField (n * ℓ.side) => bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c := by
  obtain ⟨hR, -, hS, -, hC, -⟩ := hB ℓ 0 n
  set f : TorusField (n * ℓ.side) → ℍ[ℝ] :=
    fun W => bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c with hf
  refine measurable_of_isOpen fun U hU => ?_
  have hcov : f ⁻¹' U = ⋃ H ∈ Set.range fun W : TorusField (n * ℓ.side) => fineHotLumps ℓ (fineLevelField ℓ n W),
      ({W : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n W) = H} ∩ f ⁻¹' U) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨W, rfl⟩, rfl, h⟩
    · rintro ⟨_, _, _, h⟩
      exact h
  rw [hcov]
  refine MeasurableSet.biUnion hR.countable fun H _ => ?_
  have hc : ContinuousOn f {W : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n W) = H} :=
    hC H b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  have h1 : IsOpen (({W : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n W) = H}).restrict f ⁻¹' U) :=
    hU.preimage (continuousOn_iff_continuous_restrict.1 hc)
  have h3 := (hS H).subtype_image h1.measurableSet
  convert h3 using 1
  ext W
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, Set.restrict_apply,
    Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, h'⟩
theorem fitConditionalMean_eq_integral (ℓ : StepParameters) (x : ℝ) (W : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    fitConditionalMean ℓ x W b c = ∫ g, fitOfElement ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c g *
      kernelOfElement ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b c g ∂haarUnit := by
  unfold fitConditionalMean
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show bondFit ℓ W _ b c * bondKernelAt ℓ x W _ b c = _
  rw [bondFit_eq_fitOfElement, bondKernelAt_eq_kernelOfElement, fieldAtBond_apply_self]
theorem bondScoreProperties_holds (hK : BondKernelProperties) (hB : BondKernelBorel) :
    BondScoreProperties := by
  intro ℓ hfit x n _ b c
  have ha : ℓ.coupling ≠ 0 := by
    have := hfit.a_ge
    linarith
  refine ⟨fun W => fitConditionalMean_eq hK ℓ ha x W b c, fun W V => ?_, fun W V => ?_, fun W V => ?_, ?_⟩
  · rw [bondScore, bondFit_eq_fitOfElement, fitConditionalMean_eq hK ℓ ha, deriv_logPartitionGap hK,
      meanNorm_eq_norm_bondMean]
    simp only [fitOfElement]
    ring
  · set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
    have hk0 : ∀ g, 0 ≤ kernelOfElement ℓ x w b c g := fun g =>
      div_nonneg (Real.exp_pos _).le (partitionFn_pos hK _).le
    have hf : ∀ g, 0 ≤ fitOfElement ℓ w b c g ∧ fitOfElement ℓ w b c g ≤ 2 := by
      intro g
      have h1 := abs_le.mp (abs_re_mul_inv_le (bondMean ℓ w b c) g)
      have h2 := norm_bondMean_le ℓ w b c
      simp only [fitOfElement]
      constructor <;> linarith [h1.1, h1.2]
    have hkc := continuous_kernelOfElement ℓ x w b c
    have hfc := continuous_fitOfElement ℓ w b c
    have hm := fitConditionalMean_eq_integral ℓ x W b c
    have hm0 : 0 ≤ fitConditionalMean ℓ x W b c := by
      rw [hm]
      exact integral_nonneg fun g => mul_nonneg (hf g).1 (hk0 g)
    have hm2 : fitConditionalMean ℓ x W b c ≤ 2 := by
      rw [hm]
      calc ∫ g, fitOfElement ℓ w b c g * kernelOfElement ℓ x w b c g ∂haarUnit
          ≤ ∫ g, 2 * kernelOfElement ℓ x w b c g ∂haarUnit := by
            refine integral_mono ((hfc.mul hkc).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)) ((continuous_const.mul hkc).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)) fun g => ?_
            exact mul_le_mul_of_nonneg_right (hf g).2 (hk0 g)
        _ = 2 := by rw [integral_const_mul, integral_kernelOfElement hK]; norm_num
    rw [bondScore, bondFit_eq_fitOfElement, abs_le]
    constructor <;> linarith [(hf (V c.1 c.2)).1, (hf (V c.1 c.2)).2]
  · set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
    have hkc := continuous_kernelOfElement ℓ x w b c
    have hfc := continuous_fitOfElement ℓ w b c
    have he : ∀ g : UnitQuaternion, bondScore ℓ x W (fieldAtBond V c g) b c *
        bondKernelAt ℓ x W (fieldAtBond V c g) b c =
        fitOfElement ℓ w b c g * kernelOfElement ℓ x w b c g -
          fitConditionalMean ℓ x W b c * kernelOfElement ℓ x w b c g := by
      intro g
      rw [bondScore, bondFit_eq_fitOfElement, bondKernelAt_eq_kernelOfElement, fieldAtBond_apply_self]
      ring
    simp only [he]
    have hi1 : Integrable (fun g => fitOfElement ℓ w b c g * kernelOfElement ℓ x w b c g) haarUnit :=
      (hfc.mul hkc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun g => kernelOfElement ℓ x w b c g) haarUnit :=
      hkc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul, integral_kernelOfElement hK,
      ← fitConditionalMean_eq_integral]
    ring
  · have hq := measurable_bondMean hB ℓ b c
    have hnorm : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖ := (hq.comp measurable_fst).norm
    have hel : Measurable fun p : TorusField (n * ℓ.side) × TorusField n => p.2 c.1 c.2 :=
      (measurable_pi_apply c.2).comp ((measurable_pi_apply c.1).comp measurable_snd)
    have hΨ : Continuous fun r : ℍ[ℝ] × UnitQuaternion => (r.1 * ((r.2⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
      Quaternion.continuous_re.comp (continuous_fst.mul
        (continuous_subtype_val.comp (continuous_inv.comp continuous_snd)))
    have hre : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        (bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c *
          (((p.2 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re :=
      hΨ.measurable.comp ((hq.comp measurable_fst).prodMk hel)
    have hd : Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        deriv logPartitionGap
          (ℓ.coupling * x * ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖) :=
      (measurable_deriv logPartitionGap).comp (measurable_const.mul hnorm)
    have he : (fun p : TorusField (n * ℓ.side) × TorusField n => bondScore ℓ x p.1 p.2 b c) = fun p =>
        (‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖ -
          (bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c *
            (((p.2 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) -
        ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖ *
          deriv logPartitionGap
            (ℓ.coupling * x * ‖bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 p.1) b c‖) := by
      funext p
      rw [bondScore, bondFit_eq_fitOfElement, fitConditionalMean_eq hK ℓ ha, meanNorm_eq_norm_bondMean]
      rfl
    rw [he]
    exact (hnorm.sub hre).sub (hnorm.mul hd)
end BondScore
end YangMills.Construction.WeightedResponses
end
