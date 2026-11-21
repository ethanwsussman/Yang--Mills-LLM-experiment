import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsOfSmoothSequencesProof
import Reconstruction.MinkowskiSpace.ClosureOfTheTensorVectorsAndTheEuclideanVectors
import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFixProof
import Reconstruction.MinkowskiSpace.SeparabilityAndFixedVectorsOfTheTensorVectors
import Reconstruction.MinkowskiSpace.TimeTranslationOfTheVectorsOfSmoothSequencesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
noncomputable section
namespace YangMills.Construction.TensorHilbertSeparable
open YangMills.Construction.MinkowskiSpace YangMills.Construction.FieldForms YangMills.Construction.RealPointVectors YangMills.Construction.FieldFormHilbert YangMills.Construction.ProjectionMeasures YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.PVMCalculus
theorem norm_one_add_lt_two {a : ℂ} (ha : ‖a‖ = 1) (hne : a ≠ 1) : ‖1 + a‖ < 2 := by
  by_contra hge
  have hle : ‖1 + a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_add_le _ _
  have heq : ‖1 + a‖ = ‖(1 : ℂ)‖ + ‖a‖ := by
    rw [norm_one, ha] at hle ⊢
    linarith
  have hray : SameRay ℝ (1 : ℂ) a := sameRay_iff_norm_add.2 heq
  have hn : ‖(1 : ℂ)‖ = ‖a‖ := by rw [norm_one, ha]
  exact hne ((sameRay_iff_of_norm_eq hn).1 hray).symm
theorem norm_third_sum_lt_one {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ 1 ∨ b ≠ 1) :
    ‖(1 : ℂ) * ((1 / 3 : ℂ) * 1 + (1 / 3 : ℂ) * a) + (1 / 3 : ℂ) * b‖ < 1 := by
  have he : (1 : ℂ) * ((1 / 3 : ℂ) * 1 + (1 / 3 : ℂ) * a) + (1 / 3 : ℂ) * b =
      (1 / 3 : ℂ) * (1 + a + b) := by ring
  have hthird : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  have hsum : ‖1 + a + b‖ < 3 := by
    rcases hab with hab | hab
    · have h₁ := norm_one_add_lt_two ha hab
      have h₂ := norm_add_le (1 + a) b
      rw [hb] at h₂
      linarith
    · have h₁ := norm_one_add_lt_two hb hab
      have h₂ := norm_add_le (1 + b) a
      rw [ha] at h₂
      have hswap : 1 + a + b = 1 + b + a := by ring
      rw [hswap]
      linarith
  rw [he, norm_mul, hthird]
  linarith
theorem eq_zero_of_cexp_I_mul_eq_one_of_sqrt_two {x : ℝ}
    (h₁ : Complex.exp (Complex.I * ((1 * x : ℝ) : ℂ)) = 1)
    (h₂ : Complex.exp (Complex.I * ((Real.sqrt 2 * x : ℝ) : ℂ)) = 1) : x = 0 := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h₁
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h₂
  have hm' : x = m * (2 * Real.pi) := by
    have : ((x : ℝ) : ℂ) = ((m * (2 * Real.pi) : ℝ) : ℂ) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      push_cast at hm ⊢
      rw [one_mul] at hm
      rw [hm]
      ring
    exact_mod_cast this
  have hk' : Real.sqrt 2 * x = k * (2 * Real.pi) := by
    have : ((Real.sqrt 2 * x : ℝ) : ℂ) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      rw [hk]
      push_cast
      ring
    exact_mod_cast this
  by_contra hx
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0
    apply hx
    rw [hm', h0, zero_mul]
  have htwopi : (2 * Real.pi) ≠ 0 := by positivity
  apply irrational_sqrt_two
  refine ⟨(k : ℚ) / m, ?_⟩
  push_cast
  rw [div_eq_iff hm0]
  apply mul_right_cancel₀ htwopi
  rw [← hk', hm']
  ring
theorem minkowskiForm_smul_timeUnit (s : ℝ) (p : Fin 4 → ℝ) :
    minkowskiForm (toComplex (s • timeUnit)) (toComplex p) = ((s * p 0 : ℝ) : ℂ) := by
  simp [minkowskiForm, spaceBilin, spacePart, toComplex, timeUnit, mkTimeSpace]
def timePhase (s : ℝ) : (Fin 4 → ℝ) → ℂ :=
  closedFutureCone.indicator fun p =>
    Complex.exp (Complex.I * minkowskiForm (toComplex (s • timeUnit)) (toComplex p))
def timeDamping (t : ℝ) : (Fin 4 → ℝ) → ℂ :=
  closedFutureCone.indicator fun p =>
    Complex.exp (Complex.I * minkowskiForm (imagTimeShift t) (toComplex p))
theorem time_nonneg_of_mem_closedFutureCone {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) :
    0 ≤ p 0 := by apply _root_.YangMills.Construction.TimeTranslations.time_nonneg_of_mem_futureCone <;> assumption
theorem I_mul_minkowskiForm_imagTimeShift (t : ℝ) (p : Fin 4 → ℝ) :
    Complex.I * minkowskiForm (imagTimeShift t) (toComplex p) = ((-(t * p 0) : ℝ) : ℂ) := by
  rw [imagTimeShift, minkowskiForm_smul_left, minkowskiForm_smul_timeUnit, ← mul_assoc,
    Complex.I_mul_I]
  push_cast
  ring
theorem norm_timePhase_of_mem (s : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) :
    ‖timePhase s p‖ = 1 := by
  rw [timePhase, Set.indicator_of_mem hp, minkowskiForm_smul_timeUnit, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
theorem norm_timePhase_le_one (s : ℝ) (p : Fin 4 → ℝ) : ‖timePhase s p‖ ≤ 1 := by
  by_cases hp : p ∈ closedFutureCone
  · exact (norm_timePhase_of_mem s hp).le
  · rw [timePhase, Set.indicator_of_notMem hp, norm_zero]
    exact zero_le_one
theorem measurable_timePhase (s : ℝ) : Measurable (timePhase s) := by
  have hf : (fun p : Fin 4 → ℝ =>
      Complex.exp (Complex.I * minkowskiForm (toComplex (s • timeUnit)) (toComplex p))) =
      fun p => Complex.exp (Complex.I * ((s * p 0 : ℝ) : ℂ)) := by
    funext p
    rw [minkowskiForm_smul_timeUnit]
  have hc : Continuous fun p : Fin 4 → ℝ => Complex.exp (Complex.I * ((s * p 0 : ℝ) : ℂ)) := by
    fun_prop
  rw [timePhase, hf]
  exact hc.measurable.indicator YangMills.Construction.WightmanTheory.closedFutureConeBorel.2
theorem isBddMeasurableFun_timePhase (s : ℝ) : IsBddMeasurableFun (timePhase s) :=
  ⟨measurable_timePhase s, 1, norm_timePhase_le_one s⟩
theorem isBddMeasurableFun_timeDamping {t : ℝ} (ht : 0 ≤ t) :
    IsBddMeasurableFun (timeDamping t) := by
  have hf : (fun p : Fin 4 → ℝ =>
      Complex.exp (Complex.I * minkowskiForm (imagTimeShift t) (toComplex p))) =
      fun p => Complex.exp ((-(t * p 0) : ℝ) : ℂ) := by
    funext p
    rw [I_mul_minkowskiForm_imagTimeShift]
  have hc : Continuous fun p : Fin 4 → ℝ => Complex.exp ((-(t * p 0) : ℝ) : ℂ) := by
    fun_prop
  refine ⟨?_, 1, fun p => ?_⟩
  · rw [timeDamping, hf]
    exact hc.measurable.indicator YangMills.Construction.WightmanTheory.closedFutureConeBorel.2
  · by_cases hp : p ∈ closedFutureCone
    · rw [timeDamping, Set.indicator_of_mem hp, I_mul_minkowskiForm_imagTimeShift,
        Complex.norm_exp, Complex.ofReal_re, Real.exp_le_one_iff]
      have := mul_nonneg ht (time_nonneg_of_mem_closedFutureCone hp)
      linarith
    · rw [timeDamping, Set.indicator_of_notMem hp, norm_zero]
      exact zero_le_one
def halfPhaseAverage : (Fin 4 → ℝ) → ℂ :=
  fun p => (1 / 3 : ℂ) * 1 + (1 / 3 : ℂ) * timePhase 1 p
def phaseAverage : (Fin 4 → ℝ) → ℂ :=
  fun p => (1 : ℂ) * halfPhaseAverage p + (1 / 3 : ℂ) * timePhase (Real.sqrt 2) p
theorem measurable_halfPhaseAverage : Measurable halfPhaseAverage :=
  measurable_const.add (measurable_const.mul (measurable_timePhase 1))
theorem isBddMeasurableFun_halfPhaseAverage : IsBddMeasurableFun halfPhaseAverage := by
  refine ⟨measurable_halfPhaseAverage, 2 / 3, fun p => ?_⟩
  have h₁ := norm_timePhase_le_one 1 p
  have hthird : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  have h₂ := norm_add_le ((1 / 3 : ℂ) * 1) ((1 / 3 : ℂ) * timePhase 1 p)
  rw [norm_mul, norm_mul, hthird, norm_one] at h₂
  refine h₂.trans ?_
  linarith
theorem measurable_phaseAverage : Measurable phaseAverage :=
  (measurable_const.mul measurable_halfPhaseAverage).add
    (measurable_const.mul (measurable_timePhase _))
theorem norm_phaseAverage_le_one (p : Fin 4 → ℝ) : ‖phaseAverage p‖ ≤ 1 := by
  have h₁ := norm_timePhase_le_one 1 p
  have h₂ := norm_timePhase_le_one (Real.sqrt 2) p
  have hthird : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  have h₃ : ‖phaseAverage p‖ ≤ ‖(1 : ℂ) * halfPhaseAverage p‖ +
      ‖(1 / 3 : ℂ) * timePhase (Real.sqrt 2) p‖ := norm_add_le _ _
  have h₄ : ‖halfPhaseAverage p‖ ≤ ‖(1 / 3 : ℂ) * 1‖ + ‖(1 / 3 : ℂ) * timePhase 1 p‖ :=
    norm_add_le _ _
  rw [norm_mul, norm_mul, hthird, norm_one, one_mul] at h₃
  rw [norm_mul, norm_mul, hthird, norm_one] at h₄
  linarith
theorem isBddMeasurableFun_phaseAverage : IsBddMeasurableFun phaseAverage :=
  ⟨measurable_phaseAverage, 1, norm_phaseAverage_le_one⟩
theorem isBddMeasurableFun_phaseAverage_pow (j : ℕ) :
    IsBddMeasurableFun fun p => phaseAverage p ^ j := by
  refine ⟨measurable_phaseAverage.pow_const j, 1, fun p => ?_⟩
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_phaseAverage_le_one p)
def zeroEnergyIndicator : (Fin 4 → ℝ) → ℂ :=
  (closedFutureCone ∩ {p | p 0 = 0}).indicator fun _ => (1 : ℂ)
theorem isBddMeasurableFun_zeroEnergyIndicator : IsBddMeasurableFun zeroEnergyIndicator := by
  have hs : MeasurableSet (closedFutureCone ∩ {p : Fin 4 → ℝ | p 0 = 0}) :=
    YangMills.Construction.WightmanTheory.closedFutureConeBorel.2.inter
      (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
  refine ⟨measurable_const.indicator hs, 1, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone ∩ {p | p 0 = 0}
  · rw [zeroEnergyIndicator, Set.indicator_of_mem hp, norm_one]
  · rw [zeroEnergyIndicator, Set.indicator_of_notMem hp, norm_zero]
    exact zero_le_one
theorem timePhase_of_time_eq_zero (s : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone)
    (h0 : p 0 = 0) : timePhase s p = 1 := by
  rw [timePhase, Set.indicator_of_mem hp, minkowskiForm_smul_timeUnit, h0]
  simp
theorem tendsto_phaseAverage_pow {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) :
    Tendsto (fun j : ℕ => phaseAverage p ^ j) atTop (𝓝 (zeroEnergyIndicator p)) := by
  by_cases h0 : p 0 = 0
  · have hw : phaseAverage p = 1 := by
      simp only [phaseAverage, halfPhaseAverage, timePhase_of_time_eq_zero _ hp h0]
      norm_num
    have hz : zeroEnergyIndicator p = 1 := by
      rw [zeroEnergyIndicator, Set.indicator_of_mem (show p ∈ closedFutureCone ∩ {p | p 0 = 0} from
        ⟨hp, h0⟩)]
    simp [hw, hz]
  · have hz : zeroEnergyIndicator p = 0 :=
      Set.indicator_of_notMem (fun h => h0 h.2) _
    rw [hz]
    refine tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
    refine norm_third_sum_lt_one (norm_timePhase_of_mem 1 hp) (norm_timePhase_of_mem _ hp) ?_
    by_contra hall
    push Not at hall
    apply h0
    apply eq_zero_of_cexp_I_mul_eq_one_of_sqrt_two
    · have h := hall.1
      rwa [timePhase, Set.indicator_of_mem hp, minkowskiForm_smul_timeUnit] at h
    · have h := hall.2
      rwa [timePhase, Set.indicator_of_mem hp, minkowskiForm_smul_timeUnit] at h
theorem timeDamping_mul_zeroEnergyIndicator (t : ℝ) :
    (fun p => timeDamping t p * zeroEnergyIndicator p) = zeroEnergyIndicator := by
  funext p
  by_cases hp : p ∈ closedFutureCone ∩ {p | p 0 = 0}
  · have h0 : p 0 = 0 := hp.2
    rw [timeDamping, Set.indicator_of_mem hp.1, I_mul_minkowskiForm_imagTimeShift, h0]
    simp
  · simp [zeroEnergyIndicator, Set.indicator_of_notMem hp]
section FixedVectors
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K}
theorem spectralTranslation_imagTimeShift (t : ℝ) :
    spectralTranslation E (imagTimeShift t) = pvmIntegral E (timeDamping t) :=
  rfl
theorem pvmIntegral_phaseAverage_apply
    (hI : PvmIntegralBasic E YangMills.Construction.WightmanTheory.closedFutureConeBorel)
    (hR : PvmIntegralRules E) {χ : K}
    (h₁ : pvmIntegral E (timePhase 1) χ = χ)
    (h₂ : pvmIntegral E (timePhase (Real.sqrt 2)) χ = χ) :
    pvmIntegral E phaseAverage χ = χ := by
  have hone : IsBddMeasurableFun fun _ : Fin 4 → ℝ => (1 : ℂ) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have hw : pvmIntegral E phaseAverage =
      (1 : ℂ) • pvmIntegral E halfPhaseAverage +
        (1 / 3 : ℂ) • pvmIntegral E (timePhase (Real.sqrt 2)) :=
    hI.2 1 (1 / 3) halfPhaseAverage (timePhase (Real.sqrt 2)) isBddMeasurableFun_halfPhaseAverage
      (isBddMeasurableFun_timePhase _)
  have hh : pvmIntegral E halfPhaseAverage =
      (1 / 3 : ℂ) • pvmIntegral E (fun _ => (1 : ℂ)) +
        (1 / 3 : ℂ) • pvmIntegral E (timePhase 1) :=
    hI.2 (1 / 3) (1 / 3) (fun _ => 1) (timePhase 1) hone (isBddMeasurableFun_timePhase 1)
  rw [hw, hh, hR.2.2.2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, h₁, h₂]
  module
theorem pvmIntegral_phaseAverage_pow_apply
    (hR : PvmIntegralRules E) {χ : K} (hw : pvmIntegral E phaseAverage χ = χ)
    (j : ℕ) : pvmIntegral E (fun p => phaseAverage p ^ j) χ = χ := by
  induction j with
  | zero =>
    simp only [pow_zero]
    rw [hR.2.2.2]
    rfl
  | succ j ih =>
    have hmul := hR.1 (fun p => phaseAverage p ^ j) phaseAverage
      (isBddMeasurableFun_phaseAverage_pow j) isBddMeasurableFun_phaseAverage
    simp only [← pow_succ] at hmul
    rw [hmul]
    show pvmIntegral E (fun p => phaseAverage p ^ j) (pvmIntegral E phaseAverage χ) = χ
    rw [hw, ih]
theorem imagTimeShift_fixes_of_real_translations_fix
    (hI : PvmIntegralBasic E YangMills.Construction.WightmanTheory.closedFutureConeBorel)
    (hR : PvmIntegralRules E)
    (hN : PvmIntegralNormAndConvergence E YangMills.Construction.WightmanTheory.closedFutureConeBorel)
    {χ : K} (hfix : ∀ a : RealVec4, spectralTranslation E (toComplex a) χ = χ) {t : ℝ}
    (ht : 0 ≤ t) : spectralTranslation E (imagTimeShift t) χ = χ := by
  have hw : pvmIntegral E phaseAverage χ = χ :=
    pvmIntegral_phaseAverage_apply hI hR (hfix _) (hfix _)
  have hpow := pvmIntegral_phaseAverage_pow_apply hR hw
  have hlim := (hN.2 ℕ (fun j p => phaseAverage p ^ j) id zeroEnergyIndicator
    isBddMeasurableFun_phaseAverage_pow
    ⟨1, fun j p _ => by
      simpa using pow_le_one₀ (norm_nonneg _) (norm_phaseAverage_le_one p) (n := j)⟩
    (fun p hp => tendsto_phaseAverage_pow hp)).2 isBddMeasurableFun_zeroEnergyIndicator χ
  have hz : pvmIntegral E zeroEnergyIndicator χ = χ := by
    refine tendsto_nhds_unique hlim ?_
    simp only [id, hpow]
    exact tendsto_const_nhds
  have hprod := hR.1 (timeDamping t) zeroEnergyIndicator (isBddMeasurableFun_timeDamping ht)
    isBddMeasurableFun_zeroEnergyIndicator
  rw [timeDamping_mul_zeroEnergyIndicator] at hprod
  have happ := DFunLike.congr_fun hprod χ
  rw [spectralTranslation_imagTimeShift]
  have happ' : pvmIntegral E zeroEnergyIndicator χ =
      pvmIntegral E (timeDamping t) (pvmIntegral E zeroEnergyIndicator χ) := happ
  rw [hz] at happ'
  exact happ'.symm
end FixedVectors
section Separability
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
omit [CompleteSpace K] in
theorem seqClosureOf_eq_closure (D : Set K) : seqClosureOf D = closure D := by
  ext χ
  rw [mem_closure_iff_seq_limit]
  rfl
theorem wickMapTuple_mem_diffCoordsInTube {m : ℕ} {x : TestSpaces.PointTuple (m + 1)}
    (hx : x ∈ TestSpaces.increasingPositiveTimes (m + 1)) :
    wickMapTuple (tupleToComplex x) ∈ diffCoordsInTube (m + 1) := by apply _root_.YangMills.Construction.MinkowskiSpace.WickTimeShift.wickMapTuple_mem_diffCoordsInTube <;> assumption
theorem continuous_wickMapTuple_tupleToComplex (m : ℕ) :
    Continuous fun x : TestSpaces.PointTuple m => wickMapTuple (tupleToComplex x) := by apply _root_.YangMills.Construction.SmoothSeqInner.continuous_wickOfReal <;> assumption
theorem isSeparable_euclideanStates
    (hc : ∀ m : ℕ, ContinuousOn (stateVector E Ω A (m + 1)) (diffCoordsInTube (m + 1))) :
    TopologicalSpace.IsSeparable (euclideanStates E Ω A) := by
  have hU : euclideanStates E Ω A = ⋃ m : ℕ,
      (fun x : TestSpaces.PointTuple m =>
        stateVector E Ω A m (wickMapTuple (tupleToComplex x))) ''
        TestSpaces.increasingPositiveTimes m := by
    ext v
    simp only [euclideanStates, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨m, x, hx, rfl⟩
      exact ⟨m, x, hx, rfl⟩
    · rintro ⟨m, x, hx, rfl⟩
      exact ⟨m, x, hx, rfl⟩
  rw [hU]
  refine TopologicalSpace.IsSeparable.iUnion fun m => ?_
  cases m with
  | zero =>
    refine (Set.countable_singleton Ω).isSeparable.mono ?_
    rintro _ ⟨x, -, rfl⟩
    rfl
  | succ m =>
    refine ContinuousOn.isSeparable_image ?_ (TopologicalSpace.IsSeparable.of_separableSpace _)
    exact (hc m).comp (continuous_wickMapTuple_tupleToComplex (m + 1)).continuousOn
      fun x hx => wickMapTuple_mem_diffCoordsInTube hx
theorem separableSpace_tensorHilbert
    (hcl : tensorDomainClosure E Ω A =
      SesquilinearForms.closedLinSpan (euclideanStates E Ω A))
    (hc : ∀ m : ℕ, ContinuousOn (stateVector E Ω A (m + 1)) (diffCoordsInTube (m + 1))) :
    TopologicalSpace.SeparableSpace (tensorHilbert E Ω A) := by
  have hs : TopologicalSpace.IsSeparable ((tensorHilbert E Ω A : Submodule ℂ K) : Set K) := by
    rw [coe_tensorHilbert, hcl, SesquilinearForms.closedLinSpan, seqClosureOf_eq_closure]
    exact ((isSeparable_euclideanStates E Ω A hc).span).closure
  exact hs.separableSpace
end Separability
theorem claim_of_closure_products_calculus
    (hClosure : RealPointVectors.TensorClosure.Statement)
    (hProducts : FieldForms.FieldProductProperties)
    (hCalc : PVMCalculus.BoundedFunctionalCalculus) : Claim := by
  intro K _ _ _ E Ω A ℘ C hF
  obtain ⟨-, -, -, -, -, -, -, hHol, -⟩ := hProducts K E Ω A ℘ C hF
  obtain ⟨-, hI, hR, hN, -⟩ := (hCalc.2 K).2 E
    YangMills.Construction.WightmanTheory.closedFutureConeBorel hF.isPVM hF.supportedOn
  refine ⟨separableSpace_tensorHilbert E Ω A (hClosure E Ω A ℘ C hF).1
    (fun m => (hHol m).2.2.2.2), fun hfix ψ hψ => ?_⟩
  exact hfix ψ fun t ht => imagTimeShift_fixes_of_real_translations_fix hI hR hN hψ ht
end YangMills.Construction.TensorHilbertSeparable
