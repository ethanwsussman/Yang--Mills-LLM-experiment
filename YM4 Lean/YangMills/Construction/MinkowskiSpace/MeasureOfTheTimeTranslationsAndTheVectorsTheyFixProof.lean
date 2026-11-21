import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFix
import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.TimeTranslations
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties
  ProjectionMeasures OneLoopNotation ComplexHilbert PVMCalculus
  MinkowskiSpace FieldForms FieldFormConditions
theorem time_nonneg_of_mem_futureCone {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) : 0 ≤ p 0 := by
  have h : 0 ≤ p 0 - spaceNorm (spacePart p) := hp
  exact (Real.sqrt_nonneg _).trans (sub_nonneg.mp h)
theorem zero_mem_futureCone : (0 : Fin 4 → ℝ) ∈ closedFutureCone := by
  show (0 : Fin 4 → ℝ) 0 - spaceNorm (spacePart (0 : Fin 4 → ℝ)) ≥ 0
  simp [spaceNorm, spacePart]
theorem eq_zero_of_mem_futureCone_of_time {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone)
    (h0 : p 0 = 0) : p = 0 := by
  have h : p 0 - spaceNorm (spacePart p) ≥ 0 := hp
  have hs : Real.sqrt (∑ i, spacePart p i ^ 2) ≤ 0 := by
    have : spaceNorm (spacePart p) ≤ 0 := by linarith
    exact this
  have hsum : ∑ i, spacePart p i ^ 2 = 0 := by
    have hnn : 0 ≤ ∑ i, spacePart p i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact le_antisymm (Real.sqrt_eq_zero'.1 (le_antisymm hs (Real.sqrt_nonneg _))) hnn
  have hi : ∀ i, spacePart p i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (spacePart p i))).1 hsum i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  funext μ
  refine Fin.cases h0 (fun i => ?_) μ
  exact hi i
theorem spacePart_flipSpace (p : Fin 4 → ℝ) : spacePart (flipSpace p) = -spacePart p := by
  funext i
  simp [flipSpace, spacePart, mkTimeSpace]
theorem flipSpace_apply_zero (p : Fin 4 → ℝ) : flipSpace p 0 = p 0 := by
  simp [flipSpace, mkTimeSpace]
theorem spaceNorm_neg (v : Fin 3 → ℝ) : spaceNorm (-v) = spaceNorm v := by
  simp [spaceNorm]
theorem flipSpace_mem_futureCone_iff (p : Fin 4 → ℝ) :
    flipSpace p ∈ closedFutureCone ↔ p ∈ closedFutureCone := by
  show flipSpace p 0 - spaceNorm (spacePart (flipSpace p)) ≥ 0 ↔
    p 0 - spaceNorm (spacePart p) ≥ 0
  rw [spacePart_flipSpace, spaceNorm_neg, flipSpace_apply_zero]
theorem measurableSet_futureCone : MeasurableSet closedFutureCone :=
  (WightmanTheory.closedFutureConeBorel).2
theorem I_mul_minkowskiForm_wick (a p : Fin 4 → ℝ) :
    Complex.I * minkowskiForm (wickMap (toComplex a)) (toComplex p) =
      -(a 3 : ℂ) * (p 0 : ℂ) -
        Complex.I * ((∑ i, (![a 0, a 1, a 2] : Fin 3 → ℝ) i * spacePart p i : ℝ) : ℂ) := by
  have h₀ : wickMap (toComplex a) 0 = Complex.I * (a 3 : ℂ) := rfl
  have h₁ : spacePart (wickMap (toComplex a)) = ![(a 0 : ℂ), (a 1 : ℂ), (a 2 : ℂ)] :=
    spacePart_wickMap _
  rw [MinkowskiSpace.minkowskiForm, h₀, h₁]
  simp only [spaceBilin, spacePart, toComplex, Fin.sum_univ_three]
  push_cast
  rw [mul_sub, ← mul_assoc, ← mul_assoc, Complex.I_mul_I]
  ring
def wickExp (a p : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * minkowskiForm (wickMap (toComplex a)) (toComplex p))
theorem measurable_wickExp (a : Fin 4 → ℝ) : Measurable (wickExp a) := by
  have hc : Continuous fun p : Fin 4 → ℝ =>
      -(a 3 : ℂ) * (p 0 : ℂ) -
        Complex.I * ((∑ i, (![a 0, a 1, a 2] : Fin 3 → ℝ) i * spacePart p i : ℝ) : ℂ) := by
    unfold spacePart
    fun_prop
  have : wickExp a = fun p : Fin 4 → ℝ => Complex.exp (-(a 3 : ℂ) * (p 0 : ℂ) -
        Complex.I * ((∑ i, (![a 0, a 1, a 2] : Fin 3 → ℝ) i * spacePart p i : ℝ) : ℂ)) := by
    funext p
    rw [wickExp, I_mul_minkowskiForm_wick]
  rw [this]
  exact (Complex.continuous_exp.comp hc).measurable
theorem norm_wickExp_le_one {a p : Fin 4 → ℝ} (ha : 0 ≤ a 3) (hp : p ∈ closedFutureCone) :
    ‖wickExp a p‖ ≤ 1 := by
  rw [wickExp, I_mul_minkowskiForm_wick, Complex.norm_exp]
  have hre : (-(a 3 : ℂ) * (p 0 : ℂ) -
      Complex.I * ((∑ i, (![a 0, a 1, a 2] : Fin 3 → ℝ) i * spacePart p i : ℝ) : ℂ)).re =
      -(a 3 * p 0) := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hre, Real.exp_le_one_iff]
  have := mul_nonneg ha (time_nonneg_of_mem_futureCone hp)
  linarith
theorem isBdd_indicator_wickExp {a : Fin 4 → ℝ} (ha : 0 ≤ a 3) :
    IsBddMeasurableFun (closedFutureCone.indicator (wickExp a)) := by
  refine ⟨(measurable_wickExp a).indicator measurableSet_futureCone, 1, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone
  · rw [Set.indicator_of_mem hp]
    exact norm_wickExp_le_one ha hp
  · rw [Set.indicator_of_notMem hp]
    simp
theorem timeSpaceVec_components (a : Fin 4 → ℝ) :
    timeSpaceVec (a 3) ![a 0, a 1, a 2] = a := by
  funext μ
  fin_cases μ <;>
    simp [timeSpaceVec, timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
theorem indicator_wickExp_comp_flipSpace (a : Fin 4 → ℝ) :
    closedFutureCone.indicator (wickExp a) ∘ flipSpace =
      closedFutureCone.indicator (laplaceFourierKernel (a 3) ![a 0, a 1, a 2]) := by
  funext p
  by_cases hp : p ∈ closedFutureCone
  · have hp' := (flipSpace_mem_futureCone_iff p).2 hp
    rw [Function.comp_apply, Set.indicator_of_mem hp', Set.indicator_of_mem hp, wickExp,
      laplaceFourierKernel, I_mul_minkowskiForm_wick, flipSpace_apply_zero, spacePart_flipSpace]
    congr 1
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    push_cast
    ring
  · have hp' : flipSpace p ∉ closedFutureCone := fun h => hp ((flipSpace_mem_futureCone_iff p).1 h)
    rw [Function.comp_apply, Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
theorem pushforward_isTranslationMeasure (hCalc : BoundedFunctionalCalculus)
    (σ : TestSpaces.SepTuple → ℝ) : PushforwardIsTranslationMeasure σ := by
  intro P hP hbelow hdict
  have hcar : IsSupportedOn P subConeSet.compl := by
    have : subConeSet.compl.compl = subConeSet :=
      Subtype.ext (compl_compl _)
    rw [IsSupportedOn, this]
    exact hbelow
  obtain ⟨-, -, -, -, hI, -⟩ := (hCalc.2 (StateSpace σ)).2 P subConeSet.compl hP hcar
  obtain ⟨hpvm, hc, hint⟩ := hI flipSpace measurable_flipSpace
  refine ⟨hpvm, hc WightmanTheory.closedFutureConeBorel fun p hp => ?_, fun F a ha => ?_⟩
  · have hp' : ¬ p 0 < spaceNorm (spacePart p) := hp
    show flipSpace p 0 - spaceNorm (spacePart (flipSpace p)) ≥ 0
    rw [spacePart_flipSpace, spaceNorm_neg, flipSpace_apply_zero]
    linarith
  · have ha' : 0 ≤ a 3 := ha
    have h := hdict F (a 3) ![a 0, a 1, a 2] ha'
    rw [timeSpaceVec_components, ← indicator_wickExp_comp_flipSpace,
      ← hint _ (isBdd_indicator_wickExp ha')] at h
    exact h
def coneDecay (t : ℝ) : (Fin 4 → ℝ) → ℂ :=
  closedFutureCone.indicator fun p => Complex.exp (-(t : ℂ) * (p 0 : ℂ))
def originIndic : (Fin 4 → ℝ) → ℂ := ({0} : Set (Fin 4 → ℝ)).indicator fun _ => (1 : ℂ)
theorem wickMap_smul_timeUnitVec (t : ℝ) :
    wickMap (toComplex (t • timeUnitVec)) = imagTimeShift t := by
  have h₀ : timeUnit 0 = 1 := rfl
  have h₁ : timeUnit 1 = 0 := rfl
  have h₂ : timeUnit 2 = 0 := rfl
  have h₃ : timeUnit 3 = 0 := rfl
  funext μ
  fin_cases μ <;>
    simp [wickMap, imagTimeShift, toComplex, timeUnitVec,
      PeriodicLattice.coordVec, TimeAxis.timeIdx, h₀, h₁, h₂, h₃]
theorem indicator_exp_imagTimeShift (t : ℝ) :
    (closedFutureCone.indicator fun p =>
        Complex.exp (Complex.I * minkowskiForm (imagTimeShift t) (toComplex p))) = coneDecay t := by
  rw [coneDecay]
  congr 1
  funext p
  rw [← wickMap_smul_timeUnitVec, I_mul_minkowskiForm_wick]
  simp [timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx, Fin.sum_univ_three]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem spectralTranslation_imagTimeShift (E : FourBorelSet → BddOp H) (t : ℝ) :
    spectralTranslation E (imagTimeShift t) = pvmIntegral E (coneDecay t) := by
  rw [spectralTranslation, indicator_exp_imagTimeShift]
theorem isBdd_coneDecay {t : ℝ} (ht : 0 ≤ t) : IsBddMeasurableFun (coneDecay t) := by
  refine ⟨Measurable.indicator (by fun_prop) measurableSet_futureCone, 1, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone
  · rw [coneDecay, Set.indicator_of_mem hp, Complex.norm_exp]
    have hre : (-(t : ℂ) * (p 0 : ℂ)).re = -(t * p 0) := by simp
    rw [hre, Real.exp_le_one_iff]
    have := mul_nonneg ht (time_nonneg_of_mem_futureCone hp)
    linarith
  · rw [coneDecay, Set.indicator_of_notMem hp]
    simp
theorem isBdd_originIndic : IsBddMeasurableFun originIndic := by
  refine ⟨measurable_const.indicator (measurableSet_singleton 0), 1, fun p => ?_⟩
  by_cases hp : p = 0
  · simp [originIndic, hp]
  · simp [originIndic, hp]
theorem coneDecay_mul_originIndic (t : ℝ) :
    (fun p => coneDecay t p * originIndic p) = originIndic := by
  funext p
  by_cases hp : p = 0
  · subst hp
    simp [coneDecay, originIndic, zero_mem_futureCone]
  · simp [originIndic, hp]
theorem coneDecay_add (s t : ℝ) : coneDecay (s + t) = fun p => coneDecay s p * coneDecay t p := by
  funext p
  by_cases hp : p ∈ closedFutureCone
  · simp only [coneDecay, Set.indicator_of_mem hp]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [coneDecay, hp]
theorem tendsto_coneDecay {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun j => coneDecay (max (τ j) 0) p) atTop (𝓝 (originIndic p)) := by
  by_cases h0 : p = 0
  · subst h0
    simp [coneDecay, originIndic, zero_mem_futureCone]
  · have hpos : 0 < p 0 := lt_of_le_of_ne (time_nonneg_of_mem_futureCone hp)
      fun h => h0 (eq_zero_of_mem_futureCone_of_time hp h.symm)
    have hlim : originIndic p = 0 := by simp [originIndic, h0]
    rw [hlim]
    have hm : Tendsto (fun j => max (τ j) 0) atTop atTop :=
      tendsto_atTop_mono (fun j => le_max_left _ _) hτ
    have hr : Tendsto (fun j => Real.exp (-(max (τ j) 0 * p 0))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (hm.atTop_mul_const hpos))
    have hc : Tendsto (fun j => ((Real.exp (-(max (τ j) 0 * p 0)) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp hr
      rw [Complex.ofReal_zero] at h
      exact h
    refine hc.congr fun j => ?_
    simp only [coneDecay, Set.indicator_of_mem hp]
    push_cast
    congr 1
    ring
section Measure
variable {E : FourBorelSet → BddOp H}
theorem originBorel_eq_pvmIntegral (hR : PvmIntegralRules E) :
    E originBorel = pvmIntegral E originIndic :=
  (hR.2.2.1 originBorel).symm
theorem coneDecay_fixes_originRange (hR : PvmIntegralRules E) {t : ℝ} (ht : 0 ≤ t) (χ : H) :
    pvmIntegral E (coneDecay t) (E originBorel χ) = E originBorel χ := by
  have h := hR.1 (coneDecay t) originIndic (isBdd_coneDecay ht) isBdd_originIndic
  rw [coneDecay_mul_originIndic] at h
  rw [originBorel_eq_pvmIntegral hR]
  exact (DFunLike.congr_fun h χ).symm
theorem tendsto_pvmIntegral_coneDecay (hR : PvmIntegralRules E)
    (hN : PvmIntegralNormAndConvergence E WightmanTheory.closedFutureConeBorel)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) (χ : H) :
    Tendsto (fun j => pvmIntegral E (coneDecay (max (τ j) 0)) χ) atTop
      (𝓝 (E originBorel χ)) := by
  have hb : ∀ t : ℝ, ∀ p, ‖coneDecay (max t 0) p‖ ≤ 1 := fun t p => by
    by_cases hp : p ∈ closedFutureCone
    · rw [coneDecay, Set.indicator_of_mem hp, Complex.norm_exp]
      have hre : (-((max t 0 : ℝ) : ℂ) * (p 0 : ℂ)).re = -(max t 0 * p 0) := by simp
      rw [hre, Real.exp_le_one_iff]
      have := mul_nonneg (le_max_right t 0) (time_nonneg_of_mem_futureCone hp)
      linarith
    · rw [coneDecay, Set.indicator_of_notMem hp]
      simp
  have h := (hN.2 ℝ (fun t => coneDecay (max t 0)) τ originIndic
    (fun t => isBdd_coneDecay (le_max_right t 0)) ⟨1, fun t p _ => hb t p⟩
    (fun p hp => tendsto_coneDecay hp hτ)).2 isBdd_originIndic χ
  rw [originBorel_eq_pvmIntegral hR]
  exact h
theorem tendsto_spectralTranslation (hR : PvmIntegralRules E)
    (hN : PvmIntegralNormAndConvergence E WightmanTheory.closedFutureConeBorel) (χ : H) :
    Tendsto (fun t : ℝ => spectralTranslation E (imagTimeShift t) χ) atTop
      (𝓝 (E originBorel χ)) := by
  refine tendsto_of_seq_tendsto fun τ hτ => ?_
  refine (tendsto_pvmIntegral_coneDecay hR hN hτ χ).congr' ?_
  filter_upwards [hτ.eventually_ge_atTop 0] with j hj
  simp only [Function.comp_apply]
  rw [spectralTranslation_imagTimeShift, max_eq_left hj]
theorem originFixed_of_fixed (hR : PvmIntegralRules E)
    (hN : PvmIntegralNormAndConvergence E WightmanTheory.closedFutureConeBorel)
    {t : ℝ} (ht : 0 < t) {χ : H} (h : spectralTranslation E (imagTimeShift t) χ = χ) :
    E originBorel χ = χ := by
  rw [spectralTranslation_imagTimeShift] at h
  have hmul : ∀ j : ℕ, pvmIntegral E (coneDecay (((j : ℝ) + 1) * t)) χ = χ := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      have hnn : 0 ≤ ((j : ℝ) + 1) * t := by positivity
      have hsplit : (((j + 1 : ℕ) : ℝ) + 1) * t = t + ((j : ℝ) + 1) * t := by
        push_cast
        ring
      rw [hsplit, coneDecay_add, hR.1 _ _ (isBdd_coneDecay ht.le) (isBdd_coneDecay hnn)]
      show pvmIntegral E (coneDecay t) (pvmIntegral E (coneDecay (((j : ℝ) + 1) * t)) χ) = χ
      rw [ih, h]
  have hτ : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * t) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
  have hlim := tendsto_pvmIntegral_coneDecay hR hN hτ χ
  have hconst : (fun j : ℕ => pvmIntegral E (coneDecay (max (((j : ℝ) + 1) * t) 0)) χ) =
      fun _ => χ := by
    funext j
    rw [max_eq_left (by positivity), hmul]
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
theorem fixed_of_originFixed (hR : PvmIntegralRules E) {t : ℝ} (ht : 0 ≤ t) {χ : H}
    (h : E originBorel χ = χ) : spectralTranslation E (imagTimeShift t) χ = χ := by
  have := coneDecay_fixes_originRange hR ht χ
  rw [h] at this
  rw [spectralTranslation_imagTimeShift]
  exact this
end Measure
theorem fixedIffOriginFixed_holds (hCalc : BoundedFunctionalCalculus)
    (σ : TestSpaces.SepTuple → ℝ) : FixedIffOriginFixed σ := by
  intro E hE
  obtain ⟨-, -, hR, hN, -⟩ :=
    (hCalc.2 (StateSpace σ)).2 E _ hE.isPVM hE.supportedOn
  refine ⟨fun χ => ⟨⟨fun h => ⟨1, one_pos, h 1 zero_le_one⟩, ?_⟩, ⟨?_, ?_⟩⟩,
    fun χ => tendsto_spectralTranslation hR hN χ⟩
  · rintro ⟨t, ht, h⟩ s hs
    exact fixed_of_originFixed hR hs (originFixed_of_fixed hR hN ht h)
  · rintro ⟨t, ht, h⟩
    exact originFixed_of_fixed hR hN ht h
  · exact fun h => ⟨1, one_pos, fixed_of_originFixed hR zero_le_one h⟩
theorem pushSpan_basisVec (r : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (X : SepTuple) : pushSpan r (basisVec X) = basisVec (push r X) :=
  linearExtend_basisVec _ X
theorem juxt_nil (X : SepTuple) : SepTuple.juxt X SepTuple.nil = X := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.juxt_nil <;> assumption
theorem nil_juxt (X : SepTuple) : SepTuple.juxt SepTuple.nil X = X := by apply _root_.YangMills.Construction.ReflectionPositivity.FormProperties.nil_juxt <;> assumption
theorem pushSpan_translate_mem {v : InfiniteLattice.AmbientSpace} (hv : 0 ≤ v TimeAxis.timeIdx)
    {F : FormalSpan} (hF : F ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan (translate v) F ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p76588 <;> assumption
theorem shiftedSpan_val {v : InfiniteLattice.AmbientSpace} (hv : 0 ≤ v TimeAxis.timeIdx)
    (F : PositiveSpan) : (shiftedSpan v F).1 = pushSpan (translate v) F.1 := by
  unfold shiftedSpan
  rw [dif_pos (pushSpan_translate_mem hv F.2)]
theorem unitSpan_val : unitSpan.1 = basisVec SepTuple.nil := by
  unfold unitSpan spanBasisIn
  exact congrArg Subtype.val (Module.Basis.span_apply (linearIndependent_basisVec
    TimeAxis.upperHalfSpace) ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
theorem reflectConj_unitSpan : reflectConj unitSpan = basisVec SepTuple.nil := by
  rw [reflectConj, unitSpan_val, conjugation_basisVec, pushSpan_basisVec, push_nil]
section Clustering
variable (σ : TestSpaces.SepTuple → ℝ)
theorem linearExtension_basisVec (X : SepTuple) :
    WightmanReconstruction.linearExtension σ (basisVec X) =
      (σ (TupleLists.ofList X) : ℂ) :=
  linearExtend_basisVec _ X
def matrixCoeff (A B : FormalSpan) (t : ℝ) : ℂ :=
  WightmanReconstruction.linearExtension σ (formalMul
    (pushSpan TimeAxis.timeReflection (conjugation A))
    (pushSpan (translate (t • timeUnitVec)) B))
def matrixCoeffLimit (A B : FormalSpan) : ℂ :=
  WightmanReconstruction.linearExtension σ (formalMul
      (pushSpan TimeAxis.timeReflection (conjugation A)) (basisVec SepTuple.nil)) *
    WightmanReconstruction.linearExtension σ (formalMul (basisVec SepTuple.nil) B)
variable {σ}
theorem tendsto_matrixCoeff_basis (hcl : TimeClustering σ)
    (X Y : supportedIn TimeAxis.upperHalfSpace) :
    Tendsto (matrixCoeff σ (basisVec X.1) (basisVec Y.1)) atTop
      (𝓝 (matrixCoeffLimit σ (basisVec X.1) (basisVec Y.1))) := by
  have h' := (Complex.continuous_ofReal.tendsto _).comp (hcl X Y)
  rw [Complex.ofReal_mul] at h'
  have he : matrixCoeff σ (basisVec X.1) (basisVec Y.1) = fun t : ℝ =>
      ((σ (TupleLists.ofList (SepTuple.juxt (push TimeAxis.timeReflection X.1)
        (push (translate (t • timeUnitVec)) Y.1))) : ℝ) : ℂ) := by
    funext t
    simp only [matrixCoeff, conjugation_basisVec, pushSpan_basisVec, formalMul_basisVec,
      linearExtension_basisVec]
  have hl : matrixCoeffLimit σ (basisVec X.1) (basisVec Y.1) =
      (σ (TupleLists.ofList (push TimeAxis.timeReflection X.1)) : ℂ) *
        (σ (TupleLists.ofList Y.1) : ℂ) := by
    simp only [matrixCoeffLimit, conjugation_basisVec, pushSpan_basisVec,
      formalMul_basisVec, linearExtension_basisVec, juxt_nil, nil_juxt]
  rw [he, hl]
  exact h'
theorem tendsto_matrixCoeff_basis_left (hcl : TimeClustering σ)
    (X : supportedIn TimeAxis.upperHalfSpace)
    {B : FormalSpan} (hB : B ∈ spanIn TimeAxis.upperHalfSpace) :
    Tendsto (matrixCoeff σ (basisVec X.1) B) atTop (𝓝 (matrixCoeffLimit σ (basisVec X.1) B)) := by
  induction hB using Submodule.span_induction with
  | mem x h =>
    obtain ⟨Y, rfl⟩ := h
    exact tendsto_matrixCoeff_basis hcl X Y
  | zero =>
    have h₁ : matrixCoeff σ (basisVec X.1) 0 = fun _ => 0 := by
      funext t
      simp [matrixCoeff]
    have h₂ : matrixCoeffLimit σ (basisVec X.1) 0 = 0 := by simp [matrixCoeffLimit]
    rw [h₁, h₂]
    exact tendsto_const_nhds
  | add x y _ _ hx hy =>
    have h₁ : matrixCoeff σ (basisVec X.1) (x + y) =
        fun t => matrixCoeff σ (basisVec X.1) x t + matrixCoeff σ (basisVec X.1) y t := by
      funext t
      simp [matrixCoeff]
    have h₂ : matrixCoeffLimit σ (basisVec X.1) (x + y) =
        matrixCoeffLimit σ (basisVec X.1) x + matrixCoeffLimit σ (basisVec X.1) y := by
      simp [matrixCoeffLimit, mul_add]
    rw [h₁, h₂]
    exact hx.add hy
  | smul c x _ hx =>
    have h₁ : matrixCoeff σ (basisVec X.1) (c • x) =
        fun t => c * matrixCoeff σ (basisVec X.1) x t := by
      funext t
      simp [matrixCoeff]
    have h₂ : matrixCoeffLimit σ (basisVec X.1) (c • x) =
        c * matrixCoeffLimit σ (basisVec X.1) x := by
      simp [matrixCoeffLimit]
      ring
    rw [h₁, h₂]
    exact hx.const_mul c
theorem tendsto_matrixCoeff (hcl : TimeClustering σ) {A B : FormalSpan}
    (hA : A ∈ spanIn TimeAxis.upperHalfSpace)
    (hB : B ∈ spanIn TimeAxis.upperHalfSpace) :
    Tendsto (matrixCoeff σ A B) atTop (𝓝 (matrixCoeffLimit σ A B)) := by
  induction hA using Submodule.span_induction with
  | mem x h =>
    obtain ⟨X, rfl⟩ := h
    exact tendsto_matrixCoeff_basis_left hcl X hB
  | zero =>
    have h₁ : matrixCoeff σ 0 B = fun _ => 0 := by
      funext t
      simp [matrixCoeff]
    have h₂ : matrixCoeffLimit σ 0 B = 0 := by simp [matrixCoeffLimit]
    rw [h₁, h₂]
    exact tendsto_const_nhds
  | add x y _ _ hx hy =>
    have h₁ : matrixCoeff σ (x + y) B = fun t => matrixCoeff σ x B t + matrixCoeff σ y B t := by
      funext t
      simp [matrixCoeff]
    have h₂ : matrixCoeffLimit σ (x + y) B = matrixCoeffLimit σ x B + matrixCoeffLimit σ y B := by
      simp [matrixCoeffLimit, add_mul]
    rw [h₁, h₂]
    exact hx.add hy
  | smul c x _ hx =>
    have h₁ : matrixCoeff σ (c • x) B = fun t => conj c * matrixCoeff σ x B t := by
      funext t
      simp [matrixCoeff, map_smulₛₗ, LinearMap.smul_apply]
    have h₂ : matrixCoeffLimit σ (c • x) B = conj c * matrixCoeffLimit σ x B := by
      simp [matrixCoeffLimit, map_smulₛₗ, LinearMap.smul_apply]
      ring
    rw [h₁, h₂]
    exact hx.const_mul _
end Clustering
theorem clusteringUniqueVacuum_holds (hCalc : BoundedFunctionalCalculus)
    (hComp : FormCompletion.FormCompletionIsHilbertSpace)
    (hHilb : HilbertToolkit.HilbertCompletionExtensionRiesz)
    (σ : TestSpaces.SepTuple → ℝ) (hpos : PairingPosSemidef σ) :
    ClusteringUniqueVacuum σ := by
  intro E hE hcl
  obtain ⟨-, -, hR, hN, -⟩ :=
    (hCalc.2 (StateSpace σ)).2 E _ hE.isPVM hE.supportedOn
  have hp : SesquilinearForms.IsPosSemidefForm (FieldFormConditions.pairing σ) :=
    hpos
  have hh := (hHilb.1 PositiveSpan (FieldFormConditions.pairing σ) hp).1
  have hq : FormCompletion.IsPosSemidefHermitianForm
      (FieldFormConditions.pairing σ) :=
    { add_left := hp.add_left
      smul_left := hp.smul_left
      add_right := hp.add_right
      smul_right := hp.smul_right
      hermitian := hh.conj_symm
      nonneg := fun F => (Complex.le_def.1 (hp.nonneg F)).1 }
  obtain ⟨-, hH, -⟩ := hComp PositiveSpan (FieldFormConditions.pairing σ) hq
  obtain ⟨-, -, -, -, -, -, hinner, -, hdense⟩ := hH
  have hin : ∀ F F', ⟪stateOf σ F, stateOf σ F'⟫_ℂ =
      FieldFormConditions.pairing σ F F' := hinner
  have hkey : ∀ F F', ⟪stateOf σ F, E originBorel (stateOf σ F')⟫_ℂ =
      ⟪stateOf σ F, vacuumState σ⟫_ℂ * ⟪vacuumState σ, stateOf σ F'⟫_ℂ := by
    intro F F'
    have h₁ : Tendsto (fun t : ℝ => ⟪stateOf σ F,
        spectralTranslation E (imagTimeShift t) (stateOf σ F')⟫_ℂ) atTop
        (𝓝 ⟪stateOf σ F, E originBorel (stateOf σ F')⟫_ℂ) :=
      tendsto_const_nhds.inner (tendsto_spectralTranslation hR hN _)
    have h₂ := tendsto_matrixCoeff hcl F.2 F'.2
    have hlim : matrixCoeffLimit σ F.1 F'.1 =
        ⟪stateOf σ F, vacuumState σ⟫_ℂ * ⟪vacuumState σ, stateOf σ F'⟫_ℂ := by
      rw [vacuumState, hin, hin]
      show _ = WightmanReconstruction.linearExtension σ
          (formalMul (reflectConj F) unitSpan.1) *
        WightmanReconstruction.linearExtension σ
          (formalMul (reflectConj unitSpan) F'.1)
      rw [reflectConj_unitSpan, unitSpan_val]
      rfl
    rw [hlim] at h₂
    refine tendsto_nhds_unique (h₁.congr' ?_) h₂
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hv : 0 ≤ (t • timeUnitVec) TimeAxis.timeIdx := by
      simpa [timeUnitVec, PeriodicLattice.coordVec] using ht
    rw [← wickMap_smul_timeUnitVec, hE.translate_stateOf F' (t • timeUnitVec) hv, hin]
    show WightmanReconstruction.linearExtension σ
      (formalMul (reflectConj F) (shiftedSpan (t • timeUnitVec) F').1) = _
    rw [shiftedSpan_val hv]
    rfl
  have hE₀ : ∀ F', E originBorel (stateOf σ F') =
      ⟪vacuumState σ, stateOf σ F'⟫_ℂ • vacuumState σ := by
    intro F'
    set w := E originBorel (stateOf σ F') -
      ⟪vacuumState σ, stateOf σ F'⟫_ℂ • vacuumState σ with hw
    have hclosed : IsClosed {χ : StateSpace σ | ⟪χ, w⟫_ℂ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hall : ∀ χ : StateSpace σ, ⟪χ, w⟫_ℂ = 0 := fun χ =>
      hclosed.closure_subset_iff.2 (by
        rintro _ ⟨F, rfl⟩
        show ⟪stateOf σ F, w⟫_ℂ = 0
        rw [hw, inner_sub_right, hkey, inner_smul_right, mul_comm, sub_self]) (hdense χ)
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (hall w))
  have hall : ∀ χ : StateSpace σ, E originBorel χ = ⟪vacuumState σ, χ⟫_ℂ • vacuumState σ := by
    have hclosed : IsClosed {χ : StateSpace σ |
        E originBorel χ = ⟪vacuumState σ, χ⟫_ℂ • vacuumState σ} :=
      isClosed_eq (E originBorel).continuous
        (Continuous.smul (f := fun χ : StateSpace σ => ⟪vacuumState σ, χ⟫_ℂ)
          (g := fun _ => vacuumState σ) (continuous_const.inner continuous_id) continuous_const)
    intro χ
    exact hclosed.closure_subset_iff.2 (by
      rintro _ ⟨F, rfl⟩
      exact hE₀ F) (hdense χ)
  refine ⟨hall, fun χ h => ⟨⟪vacuumState σ, χ⟫_ℂ, ?_⟩⟩
  exact (originFixed_of_fixed hR hN one_pos (h 1 zero_le_one)).symm.trans (hall χ)
theorem measureAndFixedVectors_holds (hCalc : BoundedFunctionalCalculus)
    (hComp : FormCompletion.FormCompletionIsHilbertSpace)
    (hHilb : HilbertToolkit.HilbertCompletionExtensionRiesz) :
    MeasureAndFixedVectors := fun σ _ hpos =>
  ⟨pushforward_isTranslationMeasure hCalc σ, fixedIffOriginFixed_holds hCalc σ,
    clusteringUniqueVacuum_holds hCalc hComp hHilb σ hpos⟩
end YangMills.Construction.TimeTranslations
end
