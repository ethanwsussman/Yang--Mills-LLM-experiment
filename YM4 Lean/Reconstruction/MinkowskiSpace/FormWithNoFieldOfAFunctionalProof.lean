import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.FormWithNoFieldOfAFunctional
import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFixProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ZeroFieldFormProof
theorem coe_unitSpan :
    (ReflectionPositivity.FormProperties.unitSpan : SeparatedTuples.FormalSpan) =
      SeparatedTuples.basisVec SeparatedTuples.SepTuple.nil := by apply _root_.YangMills.Construction.TimeTranslations.unitSpan_val <;> assumption
theorem shiftedSpan_unitSpan (v : Fin 4 → ℝ) :
    ReflectionPositivity.FormProperties.shiftedSpan v ReflectionPositivity.FormProperties.unitSpan =
      ReflectionPositivity.FormProperties.unitSpan := by
  have hfix : SeparatedTuples.pushSpan (SeparatedTuples.translate v)
      (ReflectionPositivity.FormProperties.unitSpan : SeparatedTuples.FormalSpan) =
      (ReflectionPositivity.FormProperties.unitSpan : SeparatedTuples.FormalSpan) := by
    rw [coe_unitSpan, SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec,
      SeparatedTuples.push_nil]
  unfold ReflectionPositivity.FormProperties.shiftedSpan
  rw [dif_pos (by rw [hfix]; exact ReflectionPositivity.FormProperties.unitSpan.2)]
  exact Subtype.ext hfix
theorem juxt_nil_nil :
    SeparatedTuples.SepTuple.juxt SeparatedTuples.SepTuple.nil SeparatedTuples.SepTuple.nil =
      SeparatedTuples.SepTuple.nil := by
  have hc : SeparatedTuples.SepTuple.Composable SeparatedTuples.SepTuple.nil
      SeparatedTuples.SepTuple.nil := fun f hf => by
    simp [SeparatedTuples.SepTuple.nil] at hf
  exact Subtype.ext (by rw [SeparatedTuples.SepTuple.juxt_val hc]; rfl)
theorem pairing_unitSpan (σ : TestSpaces.SepTuple → ℝ) (h : σ TestSpaces.sepTupleNil = 1) :
    FieldFormConditions.pairing σ ReflectionPositivity.FormProperties.unitSpan
      ReflectionPositivity.FormProperties.unitSpan = 1 := by
  rw [FieldFormConditions.pairing_eq_reflectionForm σ h,
    ReflectionPositivity.TupleForm.reflectionForm, ReflectionPositivity.TupleForm.reflectConj,
    coe_unitSpan, SeparatedTuples.conjugation_basisVec, SeparatedTuples.pushSpan,
    SeparatedTuples.linearExtend_basisVec, SeparatedTuples.push_nil,
    SeparatedTuples.formalMul_basisVec, juxt_nil_nil,
    SeparatedTuples.TupleFunctional.spanExtension, SeparatedTuples.linearExtend_basisVec,
    (FieldFormConditions.toTupleFunctional σ h).map_nil]
  simp
theorem adjointOp_zero {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    HilbertToolkit.adjointOp (0 : OneLoopNotation.BddOp K) = 0 := by
  have hs : HilbertToolkit.IsAdjointOp (0 : OneLoopNotation.BddOp K) (HilbertToolkit.adjointOp 0) :=
    Classical.epsilon_spec (p := HilbertToolkit.IsAdjointOp (0 : OneLoopNotation.BddOp K))
      ⟨0, fun x y => by simp⟩
  refine ContinuousLinearMap.ext fun x => ?_
  have hx := hs x (HilbertToolkit.adjointOp (0 : OneLoopNotation.BddOp K) x)
  simpa using hx
theorem minkowskiForm_wick_time (t : ℝ) (p : Fin 4 → ℝ) :
    MinkowskiSpace.minkowskiForm
        (MinkowskiSpace.wickMap (MinkowskiSpace.toComplex (t • FieldFormConditions.timeUnitVec)))
        (MinkowskiSpace.toComplex p) =
      Complex.I * (t : ℂ) * (p 0 : ℂ) := by
  have h3 : (t • FieldFormConditions.timeUnitVec : Fin 4 → ℝ) 3 = t := by
    simp [FieldFormConditions.timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  have h0 : (t • FieldFormConditions.timeUnitVec : Fin 4 → ℝ) 0 = 0 := by
    simp [FieldFormConditions.timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  have h1 : (t • FieldFormConditions.timeUnitVec : Fin 4 → ℝ) 1 = 0 := by
    simp [FieldFormConditions.timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  have h2 : (t • FieldFormConditions.timeUnitVec : Fin 4 → ℝ) 2 = 0 := by
    simp [FieldFormConditions.timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  unfold MinkowskiSpace.minkowskiForm MinkowskiSpace.spaceBilin MinkowskiSpace.spacePart
  rw [Fin.sum_univ_three]
  simp [MinkowskiSpace.wickMap, MinkowskiSpace.toComplex, h0, h1, h2, h3]
theorem exp_wick_time (t : ℝ) (p : Fin 4 → ℝ) :
    Complex.exp (Complex.I * MinkowskiSpace.minkowskiForm
        (MinkowskiSpace.wickMap (MinkowskiSpace.toComplex (t • FieldFormConditions.timeUnitVec)))
        (MinkowskiSpace.toComplex p)) =
      ((Real.exp (-(t * p 0)) : ℝ) : ℂ) := by
  rw [minkowskiForm_wick_time, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((t : ℂ) * (p 0 : ℂ)) * Complex.I_mul_I
theorem time_nonneg_of_mem_cone {p : Fin 4 → ℝ} (hp : p ∈ MinkowskiSpace.closedFutureCone) :
    0 ≤ p 0 := by apply _root_.YangMills.Construction.TimeTranslations.time_nonneg_of_mem_futureCone <;> assumption
theorem eq_zero_of_mem_cone_of_time_eq_zero {p : Fin 4 → ℝ}
    (hp : p ∈ MinkowskiSpace.closedFutureCone) (h0 : p 0 = 0) : p = 0 := by apply _root_.YangMills.Construction.TimeTranslations.eq_zero_of_mem_futureCone_of_time <;> assumption
theorem norm_vacuumState (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hW : HilbertWellDefined.WellDefinedStatement)
    (σ : TestSpaces.SepTuple → ℝ) (h1 : σ TestSpaces.sepTupleNil = 1)
    (hpos : FieldFormConditions.PairingPosSemidef σ) :
    ‖FieldFormConditions.vacuumState σ‖ = 1 := by
  have hq := (hW.1 _ (FieldFormConditions.pairing σ) hpos).1
  have hin := (hC _ (FieldFormConditions.pairing σ) hq).2.1.2.2.2.2.2.2.1
  have h3 : ⟪FieldFormConditions.vacuumState σ, FieldFormConditions.vacuumState σ⟫_ℂ = 1 :=
    (hin ReflectionPositivity.FormProperties.unitSpan
      ReflectionPositivity.FormProperties.unitSpan).trans (pairing_unitSpan σ h1)
  have h2 : ‖FieldFormConditions.vacuumState σ‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h3]
    simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
theorem originBorel_fixes_vacuumState (hCalc : PVMCalculus.BoundedFunctionalCalculus)
    (σ : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace σ))
    (hE : FieldFormConditions.IsTranslationMeasure σ E) :
    E FieldForms.originBorel (FieldFormConditions.vacuumState σ) =
      FieldFormConditions.vacuumState σ := by
  obtain ⟨-, -, hR, hN, -⟩ := (hCalc.2 (FieldFormConditions.StateSpace σ)).2 E
    WightmanTheory.closedFutureConeBorel hE.isPVM hE.supportedOn
  let v : ℕ → (Fin 4 → ℝ) → ℂ := fun m => MinkowskiSpace.closedFutureCone.indicator fun p =>
    Complex.exp (Complex.I * MinkowskiSpace.minkowskiForm
      (MinkowskiSpace.wickMap (MinkowskiSpace.toComplex ((m : ℝ) • FieldFormConditions.timeUnitVec)))
      (MinkowskiSpace.toComplex p))
  let u : (Fin 4 → ℝ) → ℂ := FieldForms.originBorel.1.indicator fun _ => (1 : ℂ)
  have hfun : ∀ m : ℕ, v m = MinkowskiSpace.closedFutureCone.indicator fun p =>
      ((Real.exp (-((m : ℝ) * p 0)) : ℝ) : ℂ) := fun m => by
    simp only [v, exp_wick_time]
  have hval : ∀ (m : ℕ) (p : Fin 4 → ℝ), p ∈ MinkowskiSpace.closedFutureCone →
      v m p = ((Real.exp (-((m : ℝ) * p 0)) : ℝ) : ℂ) := fun m p hp => by
    rw [hfun, Set.indicator_of_mem hp]
  have hnorm : ∀ (m : ℕ) (p : Fin 4 → ℝ), p ∈ MinkowskiSpace.closedFutureCone → ‖v m p‖ ≤ 1 :=
    fun m p hp => by
      rw [hval m p hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.exp_le_one_iff]
      have := time_nonneg_of_mem_cone hp
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg hm this]
  have hbb : ∀ m : ℕ, ProjectionMeasures.IsBddMeasurableFun (v m) := fun m => by
    refine ⟨?_, 1, fun p => ?_⟩
    · rw [hfun]
      exact (Continuous.measurable (by fun_prop)).indicator WightmanTheory.closedFutureConeBorel.2
    · by_cases hp : p ∈ MinkowskiSpace.closedFutureCone
      · exact hnorm m p hp
      · simp [v, Set.indicator_of_notMem hp]
  have hu : ProjectionMeasures.IsBddMeasurableFun u := by
    refine ⟨measurable_const.indicator FieldForms.originBorel.2, 1, fun p => ?_⟩
    by_cases hp : p ∈ FieldForms.originBorel.1
    · simp [u, Set.indicator_of_mem hp]
    · simp [u, Set.indicator_of_notMem hp]
  have hlim : ∀ p ∈ WightmanTheory.closedFutureConeBorel.1,
      Tendsto (fun j => v (id j) p) atTop (𝓝 (u p)) := fun p hp => by
    have hp' : p ∈ MinkowskiSpace.closedFutureCone := hp
    by_cases h0 : p 0 = 0
    · have hz : p = 0 := eq_zero_of_mem_cone_of_time_eq_zero hp' h0
      have hup : u p = 1 := by
        have hm : p ∈ FieldForms.originBorel.1 := hz
        simp [u, Set.indicator_of_mem hm]
      have hvp : ∀ j : ℕ, v (id j) p = 1 := fun j => by
        rw [id, hval j p hp', h0]
        simp
      simp only [hvp, hup]
      exact tendsto_const_nhds
    · have hpos : 0 < p 0 := lt_of_le_of_ne (time_nonneg_of_mem_cone hp') (Ne.symm h0)
      have hup : u p = 0 := by
        have hm : p ∉ FieldForms.originBorel.1 := fun hm => by
          have hz : p = 0 := hm
          exact h0 (by rw [hz]; rfl)
        simp [u, Set.indicator_of_notMem hm]
      have hr : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) * p 0))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hpos))
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hr
      rw [hup]
      simp only [Complex.ofReal_zero] at hc
      refine hc.congr fun j => ?_
      exact (hval j p hp').symm
  have key := (hN.2 ℕ v id u hbb ⟨1, fun t p hp => hnorm t p hp⟩ hlim).2 hu
    (FieldFormConditions.vacuumState σ)
  have hconst : ∀ j : ℕ, PVMCalculus.pvmIntegral E (v (id j)) (FieldFormConditions.vacuumState σ) =
      FieldFormConditions.vacuumState σ := fun j => by
    have h := hE.translate_stateOf ReflectionPositivity.FormProperties.unitSpan
      ((j : ℝ) • FieldFormConditions.timeUnitVec) (by
        simp [FieldFormConditions.timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx])
    rw [shiftedSpan_unitSpan] at h
    exact h
  simp only [hconst] at key
  have h := tendsto_nhds_unique key tendsto_const_nhds
  have hue : PVMCalculus.pvmIntegral E u = E FieldForms.originBorel := hR.2.2.1 FieldForms.originBorel
  rw [hue] at h
  exact h
theorem zeroFieldForm (hCalc : PVMCalculus.BoundedFunctionalCalculus)
    (hC : FormCompletion.FormCompletionIsHilbertSpace)
    (hW : HilbertWellDefined.WellDefinedStatement) :
    InsertedFieldForm.ZeroFieldForm := by
  intro σ E p C h
  exact
    { exponent_nonneg := le_rfl
      one_le_const := le_rfl
      isPVM := h.translationMeasure.isPVM
      supportedOn := h.translationMeasure.supportedOn
      norm_vacuum := norm_vacuumState hC hW σ h.isSepFunctional.1 h.posSemidef
      origin_fixes := originBorel_fixes_vacuumState hCalc σ E h.translationMeasure
      isSelfAdjoint := fun _ _ => adjointOp_zero
      shift_conj := fun _ _ _ _ => by simp
      opNorm_le := fun _ _ => by simp [OneLoopNotation.opNormOf] }
end YangMills.Construction.ZeroFieldFormProof
end
