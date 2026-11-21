import YangMills.Construction.Splines.CubicSplineBasicFacts
import YangMills.Construction.TwoPoints.SmoothedIndicatorsAndTheThreeShapes
import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints.Shapes
open YangMills.Construction.Splines (cubicSpline splineDensity)
namespace ShapesExist
structure SplineDensityFacts : Prop where
  continuous : Continuous splineDensity
  nonneg : ∀ x, 0 ≤ splineDensity x
  eq_zero_of_notMem : ∀ x, x ∉ Icc (-(1 / 8) : ℝ) (1 / 8) → splineDensity x = 0
  integral_eq_one : ∫ x, splineDensity x = 1
theorem SplineDensityFacts.integrable (hp : SplineDensityFacts) : Integrable splineDensity :=
  hp.continuous.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hp.eq_zero_of_notMem)
theorem smoothedIcc_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    smoothedIcc a b x = ∫ v in (x - b)..(x - a), splineDensity v := by
  have hpt : ∀ u, (Icc a b).indicator (1 : ℝ → ℝ) u * splineDensity (x - u) =
      (Icc a b).indicator (fun u => splineDensity (x - u)) u := by
    intro u
    by_cases hu : u ∈ Icc a b <;> simp [hu]
  unfold smoothedIcc YangMills.Construction.Splines.realConvolution
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_left (fun v => splineDensity v)]
theorem hasDerivAt_smoothedIcc (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    HasDerivAt (smoothedIcc a b) (splineDensity (x - a) - splineDensity (x - b)) x := by
  have hF : ∀ y, HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, splineDensity v) (splineDensity y) y :=
    fun y => (hp.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hfun : smoothedIcc a b = fun x => (∫ v in (0 : ℝ)..(x - a), splineDensity v) -
      ∫ v in (0 : ℝ)..(x - b), splineDensity v := by
    funext x
    rw [smoothedIcc_eq_intervalIntegral hab]
    exact (intervalIntegral.integral_interval_sub_left (hp.continuous.intervalIntegrable _ _)
      (hp.continuous.intervalIntegrable _ _)).symm
  rw [hfun]
  exact (HasDerivAt.comp_sub_const x a (hF (x - a))).sub (HasDerivAt.comp_sub_const x b (hF (x - b)))
theorem contDiff_smoothedIcc (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ 1 (smoothedIcc a b) := by
  have hder : deriv (smoothedIcc a b) = fun x => splineDensity (x - a) - splineDensity (x - b) :=
    funext fun x => (hasDerivAt_smoothedIcc hp hab x).deriv
  refine contDiff_one_iff_deriv.2 ⟨fun x => (hasDerivAt_smoothedIcc hp hab x).differentiableAt, ?_⟩
  rw [hder]
  exact (hp.continuous.comp (continuous_id.sub continuous_const)).sub
    (hp.continuous.comp (continuous_id.sub continuous_const))
theorem smoothedIcc_mem_Icc (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    smoothedIcc a b x ∈ Icc (0 : ℝ) 1 := by
  have hle : x - b ≤ x - a := by linarith
  rw [smoothedIcc_eq_intervalIntegral hab]
  refine ⟨intervalIntegral.integral_nonneg hle fun u _ => hp.nonneg u, ?_⟩
  rw [intervalIntegral.integral_of_le hle, ← hp.integral_eq_one]
  exact setIntegral_le_integral hp.integrable (Filter.Eventually.of_forall hp.nonneg)
theorem smoothedIcc_eq_zero (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) (x : ℝ)
    (hx : x ∉ Icc (a - 1 / 8) (b + 1 / 8)) : smoothedIcc a b x = 0 := by
  have hle : x - b ≤ x - a := by linarith
  have hcongr : ∫ v in (x - b)..(x - a), splineDensity v = ∫ _ in (x - b)..(x - a), (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hle] at hv
    refine hp.eq_zero_of_notMem v fun hv' => hx ?_
    constructor
    · linarith [hv.2, hv'.1]
    · linarith [hv.1, hv'.2]
  rw [smoothedIcc_eq_intervalIntegral hab, hcongr]
  simp
theorem smoothedIcc_eq_one (hp : SplineDensityFacts) {a b x : ℝ} (hlo : a + 1 / 8 ≤ x)
    (hhi : x ≤ b - 1 / 8) : smoothedIcc a b x = 1 := by
  have hab : a ≤ b := by linarith
  have hle : x - b ≤ x - a := by linarith
  rw [smoothedIcc_eq_intervalIntegral hab, intervalIntegral.integral_of_le hle,
    ← integral_Icc_eq_integral_Ioc, ← hp.integral_eq_one]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hp.eq_zero_of_notMem y fun hy' => hy ?_
  constructor
  · linarith [hy'.1]
  · linarith [hy'.2]
theorem integral_smoothedIcc (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) :
    ∫ x, smoothedIcc a b x = b - a := by
  have hind : Integrable ((Icc a b).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hconv : smoothedIcc a b =
      MeasureTheory.convolution ((Icc a b).indicator (1 : ℝ → ℝ)) splineDensity
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    rfl
  rw [hconv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hind hp.integrable, hp.integral_eq_one,
    integral_indicator_one measurableSet_Icc]
  simp [Real.volume_real_Icc_of_le hab]
theorem smoothedIccSpec_of_le (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) :
    SmoothedIccSpec a b :=
  ⟨smoothedIcc_mem_Icc hp hab, contDiff_smoothedIcc hp hab,
    hasDerivAt_smoothedIcc hp hab, smoothedIcc_eq_zero hp hab,
    fun _ hlo hhi => smoothedIcc_eq_one hp hlo hhi, integral_smoothedIcc hp hab⟩
theorem hasCompactSupport_smoothedIcc (hp : SplineDensityFacts) {a b : ℝ} (hab : a ≤ b) :
    HasCompactSupport (smoothedIcc a b) :=
  HasCompactSupport.intro isCompact_Icc (smoothedIcc_eq_zero hp hab)
theorem ofRealFun_mem_realCc1In {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {U C : Set E} (hf : ContDiff ℝ 1 f) (hC : IsCompact C) (hCU : C ⊆ U) (hzero : ∀ x, x ∉ C → f x = 0) :
    ofRealFun f ∈ realCc1In U := by
  have hts : tsupport (ofRealFun f) ⊆ C :=
    closure_minimal (fun x hx => by_contra fun hxC => hx (by simp [ofRealFun, hzero x hxC]))
      hC.isClosed
  exact ⟨⟨Complex.ofRealCLM.contDiff.comp hf, hC.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hCU⟩, fun x => Complex.ofReal_im _⟩
theorem contDiff_ofRealFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (ofRealFun f) :=
  Complex.ofRealCLM.contDiff.comp hf
theorem hasCompactSupport_ofRealFun {E : Type*} [TopologicalSpace E] {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (ofRealFun f) :=
  hf.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero
theorem bddDeriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    BddDeriv f := by
  obtain ⟨M, hM⟩ := ((contDiff_ofRealFun hf).continuous_deriv le_rfl).bounded_above_of_compact_support
    (hasCompactSupport_ofRealFun hc).deriv
  exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩
theorem gradPlaneEsup_ne_top {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) : gradPlaneEsup g ≠ ∞ := by
  obtain ⟨M, hM⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hc.fderiv ℝ)
  have hbd : ∀ y, gradPlaneNorm g y ≤ Real.sqrt (∑ _i : Fin 2, M ^ 2) := by
    intro y
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hi : ‖gradPlane g y i‖ ≤ M := by
      calc ‖gradPlane g y i‖ ≤ ‖fderiv ℝ g y‖ * ‖(Pi.single i 1 : Fin 2 → ℝ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by simpa [Pi.norm_single] using hM y
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun y => ENNReal.ofReal_le_ofReal (hbd y))
theorem contDiff_prod_coord {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun ζ : Fin 2 → ℝ => ∏ i, g (ζ i)) :=
  contDiff_prod fun i _ => hg.comp (contDiff_apply ℝ ℝ i)
theorem prod_coord_mem_Icc {g : ℝ → ℝ} (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) (ζ : Fin 2 → ℝ) :
    ∏ i, g (ζ i) ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (hg _).1,
    Finset.prod_le_one (fun _ _ => (hg _).1) fun _ _ => (hg _).2⟩
theorem prod_coord_eq_zero {g : ℝ → ℝ} {r : ℝ} (hg : ∀ x, x ∉ Icc (-r) r → g x = 0) (ζ : Fin 2 → ℝ)
    (hζ : ζ ∉ closedSquare r) : ∏ i, g (ζ i) = 0 := by
  have hex : ∃ i, ζ i ∉ Icc (-r) r := by
    by_contra hn
    exact hζ fun i _ => not_not.1 fun hi => hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hg _ hi)
theorem isCompact_closedSquare (r : ℝ) : IsCompact (closedSquare r) :=
  isCompact_univ_pi fun _ => isCompact_Icc
theorem closedSquare_subset_openSquare {r R : ℝ} (hr : r < R) : closedSquare r ⊆ openSquare R :=
  fun _ hζ i _ => ⟨by linarith [(hζ i trivial).1], by linarith [(hζ i trivial).2]⟩
theorem smoothedIcc_half_eq_zero (hp : SplineDensityFacts) (x : ℝ) (hx : x ∉ Icc (-(5 / 8) : ℝ) (5 / 8)) :
    smoothedIcc (-(1 / 2)) (1 / 2) x = 0 :=
  smoothedIcc_eq_zero hp (by norm_num) x fun ⟨hlo, hhi⟩ => hx ⟨by linarith, by linarith⟩
theorem smoothedIcc_fiveFourths_eq_zero (hp : SplineDensityFacts) (x : ℝ)
    (hx : x ∉ Icc (-(11 / 8) : ℝ) (11 / 8)) :
    smoothedIcc (-(5 / 4)) (5 / 4) x = 0 :=
  smoothedIcc_eq_zero hp (by norm_num) x fun ⟨hlo, hhi⟩ => hx ⟨by linarith, by linarith⟩
theorem planePartitionOfUnity_eq_zero (hp : SplineDensityFacts) (ζ : Fin 2 → ℝ)
    (hζ : ζ ∉ closedSquare (5 / 8)) : planePartitionOfUnity ζ = 0 :=
  prod_coord_eq_zero (smoothedIcc_half_eq_zero hp) ζ hζ
theorem planePlateau_eq_zero (hp : SplineDensityFacts) (ζ : Fin 2 → ℝ) (hζ : ζ ∉ closedSquare (11 / 8)) :
    planePlateau ζ = 0 :=
  prod_coord_eq_zero (smoothedIcc_fiveFourths_eq_zero hp) ζ hζ
theorem contDiff_planePartitionOfUnity (hp : SplineDensityFacts) : ContDiff ℝ 1 planePartitionOfUnity :=
  contDiff_prod_coord (contDiff_smoothedIcc hp (by norm_num))
theorem contDiff_planePlateau (hp : SplineDensityFacts) : ContDiff ℝ 1 planePlateau :=
  contDiff_prod_coord (contDiff_smoothedIcc hp (by norm_num))
theorem hasCompactSupport_planePartitionOfUnity (hp : SplineDensityFacts) :
    HasCompactSupport planePartitionOfUnity :=
  HasCompactSupport.intro (isCompact_closedSquare _) (planePartitionOfUnity_eq_zero hp)
theorem hasCompactSupport_planePlateau (hp : SplineDensityFacts) : HasCompactSupport planePlateau :=
  HasCompactSupport.intro (isCompact_closedSquare _) (planePlateau_eq_zero hp)
theorem hasSum_smoothedIcc_intTranslates (hp : SplineDensityFacts) (x : ℝ) :
    HasSum (fun j : ℤ => smoothedIcc (-(1 / 2)) (1 / 2) (x - j)) 1 := by
  have hU := hasSum_integral_iUnion (μ := volume) (f := splineDensity)
    (s := fun n : ℤ => Ioc (x - 1 / 2 + n) (x - 1 / 2 + n + 1))
    (fun _ => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast (x - 1 / 2))
    hp.integrable.integrableOn
  rw [iUnion_Ioc_add_intCast, Measure.restrict_univ, hp.integral_eq_one] at hU
  have hN := (Equiv.neg ℤ).hasSum_iff.2 hU
  have hfun : (fun j : ℤ => smoothedIcc (-(1 / 2)) (1 / 2) (x - j)) =
      (fun n : ℤ => ∫ y in Ioc (x - 1 / 2 + n) (x - 1 / 2 + n + 1), splineDensity y) ∘
        (Equiv.neg ℤ) := by
    funext j
    rw [smoothedIcc_eq_intervalIntegral (by norm_num), intervalIntegral.integral_of_le (by linarith)]
    simp only [Function.comp, Equiv.neg_apply, Int.cast_neg]
    congr 2
    · congr 1 <;> ring
  rw [hfun]
  exact hN
theorem hasSum_planePartitionOfUnity (hp : SplineDensityFacts) (ζ : Fin 2 → ℝ) :
    HasSum (fun k : Fin 2 → ℤ => planePartitionOfUnity (ζ - fun i => (k i : ℝ))) 1 := by
  have hs₀ := hasSum_smoothedIcc_intTranslates hp (ζ 0)
  have hs₁ := hasSum_smoothedIcc_intTranslates hp (ζ 1)
  have hnn : ∀ (x : ℝ) (j : ℤ), 0 ≤ smoothedIcc (-(1 / 2)) (1 / 2) (x - j) :=
    fun x j => (smoothedIcc_mem_Icc hp (by norm_num) _).1
  have hm := hs₀.mul hs₁ (hs₀.summable.mul_of_nonneg hs₁.summable (hnn _) (hnn _))
  rw [one_mul] at hm
  have hE := (finTwoArrowEquiv ℤ).hasSum_iff.2 hm
  have hfun : (fun k : Fin 2 → ℤ => planePartitionOfUnity (ζ - fun i => (k i : ℝ))) =
      (fun p : ℤ × ℤ => smoothedIcc (-(1 / 2)) (1 / 2) (ζ 0 - p.1) *
        smoothedIcc (-(1 / 2)) (1 / 2) (ζ 1 - p.2)) ∘ (finTwoArrowEquiv ℤ) := by
    funext k
    simp [planePartitionOfUnity, Fin.prod_univ_two, finTwoArrowEquiv]
  rw [hfun]
  exact hE
theorem integrable_planePlateau (hp : SplineDensityFacts) : Integrable planePlateau :=
  (contDiff_planePlateau hp).continuous.integrable_of_hasCompactSupport (hasCompactSupport_planePlateau hp)
theorem planePlateau_eq_one (hp : SplineDensityFacts) : ∀ ζ ∈ closedSquare 1, planePlateau ζ = 1 := by
  intro ζ hζ
  refine Finset.prod_eq_one fun i _ => smoothedIcc_eq_one hp ?_ ?_
  · linarith [(hζ i trivial).1]
  · linarith [(hζ i trivial).2]
theorem volume_real_closedSquare_one : volume.real (closedSquare 1) = 4 := by
  have hvol : volume (closedSquare 1) = ENNReal.ofReal 4 := by
    rw [closedSquare, volume_pi_pi]
    simp only [Real.volume_Icc, Fin.prod_univ_two]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  simp [Measure.real, hvol]
theorem four_le_integral_planePlateau (hp : SplineDensityFacts) : 4 ≤ ∫ ζ, planePlateau ζ := by
  have hmeas : MeasurableSet (closedSquare 1) := (isCompact_closedSquare 1).isClosed.measurableSet
  have hset : ∫ ζ in closedSquare 1, planePlateau ζ = 4 := by
    rw [setIntegral_congr_fun hmeas (planePlateau_eq_one hp), setIntegral_const, volume_real_closedSquare_one]
    simp
  rw [← hset]
  exact setIntegral_le_integral (integrable_planePlateau hp)
    (Filter.Eventually.of_forall fun ζ => (prod_coord_mem_Icc (smoothedIcc_mem_Icc hp (by norm_num)) ζ).1)
theorem isTimeBump_timeBump (hp : SplineDensityFacts) : IsTimeBump timeBump := by
  have hab : (9 / 4 : ℝ) ≤ 11 / 4 := by norm_num
  refine ⟨ofRealFun_mem_realCc1In (contDiff_smoothedIcc hp hab) (C := Icc (17 / 8) (23 / 8))
      isCompact_Icc (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
      (fun x hx => smoothedIcc_eq_zero hp hab x fun ⟨hlo, hhi⟩ => hx ⟨by linarith, by linarith⟩),
    fun x => (smoothedIcc_mem_Icc hp hab x).1, ⟨⟨5 / 2, ?_⟩, ?_⟩, ?_⟩
  · exact smoothedIcc_eq_one hp (by norm_num) (by norm_num)
  · rintro _ ⟨x, rfl⟩
    exact (smoothedIcc_mem_Icc hp hab x).2
  · have hint : ∫ x, timeBump x = 11 / 4 - 9 / 4 := integral_smoothedIcc hp hab
    rw [hint]
    norm_num
theorem derivUniformNorm_timeBump_pos (hp : SplineDensityFacts) (hzero : splineDensity 0 = 32 / 3) :
    0 < derivUniformNorm (ofRealFun timeBump) := by
  have hab : (9 / 4 : ℝ) ≤ 11 / 4 := by norm_num
  have hc : HasCompactSupport timeBump := hasCompactSupport_smoothedIcc hp hab
  have hbdd : BddDeriv timeBump :=
    bddDeriv_of_contDiff (contDiff_smoothedIcc hp hab) hc
  have hoff : splineDensity (9 / 4 - 11 / 4) = 0 := hp.eq_zero_of_notMem _ fun hy => by norm_num at hy
  have hder : deriv (ofRealFun timeBump) (9 / 4) = ((32 / 3 : ℝ) : ℂ) := by
    have hd := (hasDerivAt_smoothedIcc hp hab (9 / 4)).ofReal_comp.deriv
    rw [hoff, sub_self, hzero, sub_zero] at hd
    exact hd
  have hnorm : ‖deriv (ofRealFun timeBump) (9 / 4)‖ = 32 / 3 := by
    rw [hder, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hle : ‖deriv (ofRealFun timeBump) (9 / 4)‖ ≤ derivUniformNorm (ofRealFun timeBump) :=
    le_ciSup hbdd (9 / 4)
  linarith
end ShapesExist
theorem ShapesExist.holds
    (hs : YangMills.Construction.Splines.CubicSplineBasicFacts) :
    ShapesExist.Statement := by
  open ShapesExist in
  obtain ⟨-, ⟨-, -, hbs, hbc, -, hb0⟩, -, ⟨hp0, -, hpc, hps, hpi, -⟩⟩ := hs
  have hp : SplineDensityFacts :=
    ⟨hpc.continuous, hp0,
      fun x hx => image_eq_zero_of_notMem_tsupport fun hy => hx (hps hy), hpi⟩
  have hzero : splineDensity 0 = 32 / 3 := by
    simp [splineDensity, hb0]
  have hab : (9 / 4 : ℝ) ≤ 11 / 4 := by norm_num
  have hTC : HasCompactSupport timeBump := hasCompactSupport_smoothedIcc hp hab
  refine ⟨fun _ _ hlt => smoothedIccSpec_of_le hp hlt.le, isTimeBump_timeBump hp, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, planePlateau_eq_one hp⟩, bddDeriv_of_contDiff (contDiff_smoothedIcc hp hab) hTC,
    bddDeriv_of_contDiff hbc (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans hbs)), ?_, ?_, derivUniformNorm_timeBump_pos hp hzero,
    integrable_planePlateau hp, four_le_integral_planePlateau hp⟩
  · exact ofRealFun_mem_realCc1In (contDiff_planePartitionOfUnity hp) (isCompact_closedSquare (5 / 8))
      (closedSquare_subset_openSquare (by norm_num)) (planePartitionOfUnity_eq_zero hp)
  · exact prod_coord_mem_Icc (smoothedIcc_mem_Icc hp (by norm_num))
  · exact hasSum_planePartitionOfUnity hp
  · exact ofRealFun_mem_realCc1In (contDiff_planePlateau hp) (isCompact_closedSquare (11 / 8))
      (closedSquare_subset_openSquare (by norm_num)) (planePlateau_eq_zero hp)
  · exact prod_coord_mem_Icc (smoothedIcc_mem_Icc hp (by norm_num))
  · exact gradPlaneEsup_ne_top (contDiff_ofRealFun (contDiff_planePartitionOfUnity hp))
      (hasCompactSupport_ofRealFun (hasCompactSupport_planePartitionOfUnity hp))
  · exact gradPlaneEsup_ne_top (contDiff_ofRealFun (contDiff_planePlateau hp))
      (hasCompactSupport_ofRealFun (hasCompactSupport_planePlateau hp))
end YangMills.Construction.TwoPoints.Shapes
