import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import YangMills.Construction.Continuum.FlatFunctionsTensorsOfSubTuplesAndSmoothTuples
import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFixProof
import Reconstruction.MinkowskiSpace.UniquenessOfTheFieldOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.FieldOperatorUniqueness
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties FieldFormConditions
  ProjectionMeasures HilbertToolkit OneLoopNotation ComplexHilbert MinkowskiSpace FieldForms
  InsertedFieldForm PVMCalculus
def expDecay (t : ℝ) (p : Fin 4 → ℝ) : ℂ := ((Real.exp (-(t * p 0)) : ℝ) : ℂ)
theorem cexp_minkowskiForm_realWickPoint (t : ℝ) (p : Fin 4 → ℝ) :
    Complex.exp (Complex.I * MinkowskiSpace.minkowskiForm (realWickPoint (t • timeUnitVec))
      (MinkowskiSpace.toComplex p)) = expDecay t p := by
  have h0 : realWickPoint (t • timeUnitVec) 0 = Complex.I * t := by
    show wickMap _ 0 = _
    rw [wickMap_apply_zero]
    simp [MinkowskiSpace.toComplex, timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  have hs : spacePart (realWickPoint (t • timeUnitVec)) = 0 := by
    rw [InsertedFieldForm.realWickPoint, spacePart_wickMap]
    funext i
    fin_cases i <;>
      simp [MinkowskiSpace.toComplex, timeUnitVec, PeriodicLattice.coordVec, TimeAxis.timeIdx]
  have hform : MinkowskiSpace.minkowskiForm (realWickPoint (t • timeUnitVec))
      (MinkowskiSpace.toComplex p) = Complex.I * t * (p 0 : ℂ) := by
    rw [MinkowskiSpace.minkowskiForm, h0, hs]
    simp [spaceBilin, MinkowskiSpace.toComplex]
  rw [hform, expDecay, ← mul_assoc, ← mul_assoc, Complex.I_mul_I]
  push_cast
  congr 1
  ring
theorem zero_le_apply_zero_of_mem_closedFutureCone {p : Fin 4 → ℝ} (hp : p ∈ closedFutureCone) :
    0 ≤ p 0 := by apply _root_.YangMills.Construction.TimeTranslations.time_nonneg_of_mem_futureCone <;> assumption
section Strong
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem tendsto_spectralTranslation_one_div (hCalc : PVMCalculus.BoundedFunctionalCalculus)
    (E : FourBorelSet → BddOp H) (hE : IsPVM E)
    (hsupp : IsSupportedOn E WightmanTheory.closedFutureConeBorel) (x : H) :
    Tendsto (fun j : ℕ => spectralTranslation E
      (realWickPoint ((1 / ((j : ℝ) + 1)) • timeUnitVec)) x) atTop (𝓝 x) := by
  obtain ⟨-, -, hRules, hNorm, -⟩ := (hCalc.2 H).2 E WightmanTheory.closedFutureConeBorel hE hsupp
  let f : ℕ → (Fin 4 → ℝ) → ℂ := fun j =>
    closedFutureCone.indicator (expDecay (1 / ((j : ℝ) + 1)))
  have hset : MeasurableSet closedFutureCone := WightmanTheory.closedFutureConeBorel.2
  have hbound : ∀ (j : ℕ), ∀ p ∈ closedFutureCone, ‖f j p‖ ≤ 1 := by
    intro j p hp
    have ht : 0 ≤ 1 / ((j : ℝ) + 1) := by positivity
    have hmul := mul_nonneg ht (zero_le_apply_zero_of_mem_closedFutureCone hp)
    simp only [f, Set.indicator_of_mem hp, expDecay, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hmeas : ∀ j, IsBddMeasurableFun (f j) := by
    intro j
    refine ⟨Measurable.indicator ?_ hset, 1, fun p => ?_⟩
    · unfold expDecay
      fun_prop
    · by_cases hp : p ∈ closedFutureCone
      · exact hbound j p hp
      · simp [f, Set.indicator_of_notMem hp]
  have hpoint : ∀ p ∈ closedFutureCone,
      Tendsto (fun j => f (id j) p) atTop (𝓝 ((fun _ => (1 : ℂ)) p)) := by
    intro p hp
    have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun j : ℕ => expDecay (1 / ((j : ℝ) + 1)) p) atTop (𝓝 (expDecay 0 p)) := by
      unfold expDecay
      have hc : Continuous fun t : ℝ => ((Real.exp (-(t * p 0)) : ℝ) : ℂ) := by fun_prop
      exact (hc.tendsto 0).comp h1
    have h3 : expDecay 0 p = 1 := by simp [expDecay]
    rw [h3] at h2
    refine h2.congr fun j => ?_
    simp [f, Set.indicator_of_mem hp]
  have hone : IsBddMeasurableFun (fun _ : Fin 4 → ℝ => (1 : ℂ)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have hlim := (hNorm.2 ℕ f id (fun _ => (1 : ℂ)) hmeas ⟨1, hbound⟩ hpoint).2 hone x
  have hT : ∀ j : ℕ, spectralTranslation E
      (realWickPoint ((1 / ((j : ℝ) + 1)) • timeUnitVec)) = pvmIntegral E (f j) := by
    intro j
    rw [FieldForms.spectralTranslation]
    congr 1
    funext p
    by_cases hp : p ∈ closedFutureCone
    · simp only [f, Set.indicator_of_mem hp, cexp_minkowskiForm_realWickPoint]
    · simp only [f, Set.indicator_of_notMem hp]
  have hid : pvmIntegral E (fun _ => (1 : ℂ)) x = x := by
    rw [hRules.2.2.2]
    rfl
  rw [hid] at hlim
  exact hlim.congr fun j => by simp only [id, hT]
end Strong
theorem eqOn_zero_of_integral_smul_eq_zero {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    {u : (Fin 4 → ℝ) → ℂ} (hu : ContinuousOn u U)
    (h : ∀ g : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • u x = 0) : ∀ x ∈ U, u x = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hu.locallyIntegrableOn hU.measurableSet) h
  have hr : u =ᵐ[volume.restrict U] 0 := (ae_restrict_iff' hU.measurableSet).2 hae
  exact fun x hx => Measure.eqOn_open_of_ae_eq hr hU hu continuousOn_const hx
def ofRealFun (g : (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → ℂ := fun y => (g y : ℂ)
theorem tsupport_ofRealFun (g : (Fin 4 → ℝ) → ℝ) : tsupport (ofRealFun g) = tsupport g := by apply _root_.YangMills.Construction.FlatTensors.tsupport_ofReal_comp <;> assumption
theorem ofRealFun_mem_c1CompactSupp {g : (Fin 4 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ofRealFun g ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := by
  refine ⟨?_, ?_, Set.subset_univ _⟩
  · exact Complex.ofRealCLM.contDiff.comp (hg.of_le (by norm_cast))
  · rw [HasCompactSupport, tsupport_ofRealFun]
    exact hc
theorem inner_insertionDensity_eq_at_center (hWell : HilbertWellDefined.WellDefinedStatement)
    (σ : TestSpaces.SepTuple → ℝ) (E : FourBorelSet → BddOp (StateSpace σ))
    (A A' : ℝ → BddOp (StateSpace σ))
    (hA : HasInsertionIntegral σ E A) (hA' : HasInsertionIntegral σ E A')
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (F : PositiveSpan) (x : StateSpace σ) :
    ⟪x, insertionDensity σ E A (2 * (s + t)) s (stateOf σ F) ((s + t) • timeUnitVec)⟫_ℂ =
      ⟪x, insertionDensity σ E A' (2 * (s + t)) s (stateOf σ F)
        ((s + t) • timeUnitVec)⟫_ℂ := by
  set c : ℝ := 2 * (s + t) with hcdef
  set y₀ : Fin 4 → ℝ := (s + t) • timeUnitVec with hy₀
  set v := stateOf σ F with hv
  have hc : 0 < c := by positivity
  have hsc : s < c / 2 := by rw [hcdef]; linarith
  have htime : y₀ TimeAxis.timeIdx = s + t := by
    simp [hy₀, timeUnitVec, PeriodicLattice.coordVec]
  have hball : ∀ y ∈ Metric.closedBall y₀ (t / 2),
      s < y TimeAxis.timeIdx ∧ y TimeAxis.timeIdx < c - s := by
    intro y hy
    have h1 : ‖(y - y₀) TimeAxis.timeIdx‖ ≤ ‖y - y₀‖ := norm_le_pi_norm _ _
    have h2 : ‖y - y₀‖ ≤ t / 2 := by simpa [dist_eq_norm] using hy
    have h3 : |y TimeAxis.timeIdx - (s + t)| ≤ t / 2 := by
      have : ‖(y - y₀) TimeAxis.timeIdx‖ = |y TimeAxis.timeIdx - (s + t)| := by
        rw [Pi.sub_apply, htime, Real.norm_eq_abs]
      linarith
    have h4 := abs_le.1 h3
    rw [hcdef]
    constructor <;> linarith [h4.1, h4.2]
  have key : ∀ g : (Fin 4 → ℝ) → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Metric.closedBall y₀ (t / 2) →
      ContinuousOn (fun y => ⟪x, insertionDensity σ E A c s v y⟫_ℂ) (tsupport g) ∧
      ContinuousOn (fun y => ⟪x, insertionDensity σ E A' c s v y⟫_ℂ) (tsupport g) ∧
      ∫ y in tsupport g, ofRealFun g y * ⟪x, insertionDensity σ E A c s v y⟫_ℂ =
        ∫ y in tsupport g, ofRealFun g y * ⟪x, insertionDensity σ E A' c s v y⟫_ℂ := by
    intro g hg hgc hgs
    have hmem := ofRealFun_mem_c1CompactSupp hg hgc
    have hsupp : ∀ y ∈ tsupport (ofRealFun g),
        s < y TimeAxis.timeIdx ∧ y TimeAxis.timeIdx < c - s := by
      intro y hy
      rw [tsupport_ofRealFun] at hy
      exact hball y (hgs hy)
    obtain ⟨hm, hw, he⟩ := hA c s hc hs hsc (ofRealFun g) hmem hsupp F
    obtain ⟨hm', hw', he'⟩ := hA' c s hc hs hsc (ofRealFun g) hmem hsupp F
    have hW := (hWell.2.2.2 _ _ _ _ _ hw).1 x
    have hW' := (hWell.2.2.2 _ _ _ _ _ hw').1 x
    have hsame := he.symm.trans he'
    rw [hsame, hW'] at hW
    rw [tsupport_ofRealFun] at hW
    have hcont := hw.continuousOn_inner x
    have hcont' := hw'.continuousOn_inner x
    rw [tsupport_ofRealFun] at hcont hcont'
    exact ⟨hcont, hcont', hW.symm⟩
  let b : ContDiffBump y₀ := ⟨t / 4, t / 2, by positivity, by linarith⟩
  have hbt : tsupport b = Metric.closedBall y₀ (t / 2) := b.tsupport_eq
  obtain ⟨hc1, hc2, -⟩ := key b b.contDiff b.hasCompactSupport hbt.le
  rw [hbt] at hc1 hc2
  have hu : ContinuousOn (fun y => ⟪x, insertionDensity σ E A c s v y⟫_ℂ -
      ⟪x, insertionDensity σ E A' c s v y⟫_ℂ) (Metric.ball y₀ (t / 2)) :=
    (hc1.sub hc2).mono Metric.ball_subset_closedBall
  have hvan := eqOn_zero_of_integral_smul_eq_zero Metric.isOpen_ball hu (fun g hg hgc hgs => ?_) y₀
    (Metric.mem_ball_self (by positivity))
  · exact sub_eq_zero.1 hvan
  obtain ⟨k1, k2, k3⟩ := key g hg hgc (hgs.trans Metric.ball_subset_closedBall)
  have hK : IsCompact (tsupport g) := hgc
  have hcg : ContinuousOn (ofRealFun g) (tsupport g) :=
    (Complex.continuous_ofReal.comp hg.continuous).continuousOn
  have i1 := (hcg.mul k1).integrableOn_compact (μ := volume) hK
  have i2 := (hcg.mul k2).integrableOn_compact (μ := volume) hK
  have hsub : ∫ y in tsupport g, (ofRealFun g y * ⟪x, insertionDensity σ E A c s v y⟫_ℂ -
      ofRealFun g y * ⟪x, insertionDensity σ E A' c s v y⟫_ℂ) = 0 := (integral_sub i1 i2).trans (sub_eq_zero.2 k3)
  have hfun : (fun z => g z • (⟪x, insertionDensity σ E A c s v z⟫_ℂ -
      ⟪x, insertionDensity σ E A' c s v z⟫_ℂ)) =
      fun y => ofRealFun g y * ⟪x, insertionDensity σ E A c s v y⟫_ℂ -
        ofRealFun g y * ⟪x, insertionDensity σ E A' c s v y⟫_ℂ := by
    funext z
    rw [Complex.real_smul, mul_sub]
    rfl
  rw [hfun, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport g), hsub]
  intro z hz
  simp [ofRealFun, image_eq_zero_of_notMem_tsupport hz]
theorem conj_spectralTranslation_eq (hWell : HilbertWellDefined.WellDefinedStatement)
    (σ : TestSpaces.SepTuple → ℝ) (hpos : PairingPosSemidef σ)
    (E : FourBorelSet → BddOp (StateSpace σ))
    (A A' : ℝ → BddOp (StateSpace σ))
    (hA : HasInsertionIntegral σ E A) (hA' : HasInsertionIntegral σ E A')
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    spectralTranslation E (realWickPoint (t • timeUnitVec)) * A s *
        spectralTranslation E (realWickPoint (t • timeUnitVec)) =
      spectralTranslation E (realWickPoint (t • timeUnitVec)) * A' s *
        spectralTranslation E (realWickPoint (t • timeUnitVec)) := by
  have h1 : (s + t) • timeUnitVec - s • timeUnitVec = t • timeUnitVec := by module
  have h2 : (2 * (s + t) - s) • timeUnitVec - (s + t) • timeUnitVec = t • timeUnitVec := by module
  obtain ⟨cl, hcl, hpair⟩ := (hWell.1 _ (FieldFormConditions.pairing σ) hpos).2
  have hd : DenseRange cl := by
    have := hpair.denseRange
    rw [ComplexHilbert.IsDenseSet, seqClosureOf_eq_closure] at this
    exact dense_iff_closure_eq.2 this
  refine DFunLike.coe_injective (hd.equalizer (ContinuousLinearMap.continuous _)
    (ContinuousLinearMap.continuous _) (funext fun F => ?_))
  refine ext_inner_left ℂ fun x => ?_
  have hk := inner_insertionDensity_eq_at_center hWell σ E A A' hA hA' hs ht F x
  simp only [insertionDensity, h1, h2] at hk
  simp only [Function.comp_apply, hcl]
  exact hk
theorem unique_holds (hCalc : PVMCalculus.BoundedFunctionalCalculus)
    (hWell : HilbertWellDefined.WellDefinedStatement) : FieldOperatorUniqueness.Unique := by
  intro σ E p C hcond A A' hA hA' s hs
  let T : ℕ → BddOp (StateSpace σ) := fun j =>
    spectralTranslation E (realWickPoint ((1 / ((j : ℝ) + 1)) • timeUnitVec))
  have hlim : ∀ x, Tendsto (fun j => T j x) atTop (𝓝 x) := fun x =>
    tendsto_spectralTranslation_one_div hCalc E hcond.translationMeasure.isPVM hcond.translationMeasure.supportedOn x
  obtain ⟨b, hb⟩ := banach_steinhaus (g := T) fun x => by
    obtain ⟨b, hb⟩ := (hlim x).norm.bddAbove_range
    exact ⟨b, fun j => hb ⟨j, rfl⟩⟩
  have hconv : ∀ (B : BddOp (StateSpace σ)) (x : StateSpace σ),
      Tendsto (fun j => (T j * B * T j) x) atTop (𝓝 (B x)) := by
    intro B x
    have hw : Tendsto (fun j => B (T j x)) atTop (𝓝 (B x)) :=
      (B.continuous.tendsto x).comp (hlim x)
    rw [tendsto_iff_norm_sub_tendsto_zero] at hw ⊢
    have hz := tendsto_iff_norm_sub_tendsto_zero.1 (hlim (B x))
    have hsum : Tendsto (fun j => b * ‖B (T j x) - B x‖ + ‖T j (B x) - B x‖) atTop (𝓝 0) := by
      simpa using (hw.const_mul b).add hz
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hsum
    have hsplit : (T j * B * T j) x - B x = T j (B (T j x) - B x) + (T j (B x) - B x) := by
      simp [map_sub]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact ((T j).le_opNorm _).trans (by gcongr; exact hb j)
  refine ContinuousLinearMap.ext fun x => ?_
  have heq : ∀ j, (T j * A s * T j) x = (T j * A' s * T j) x := fun j => by
    have := conj_spectralTranslation_eq hWell σ hcond.posSemidef E A A' hA hA' hs
      (t := 1 / ((j : ℝ) + 1)) (by positivity)
    exact DFunLike.congr_fun this x
  exact tendsto_nhds_unique (hconv (A' s) x) ((hconv (A s) x).congr heq)
end YangMills.Construction.FieldOperatorUniqueness
end
