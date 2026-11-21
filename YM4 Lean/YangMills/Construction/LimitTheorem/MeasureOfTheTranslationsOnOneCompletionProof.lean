import YangMills.Construction.LimitTheorem.MeasureOfTheTranslationsOnOneCompletion
import YangMills.Construction.MinkowskiSpace.MeasureOfTheTimeTranslationsAndTheVectorsTheyFix
import YangMills.Construction.ReflectionPositivity.ComplementsToTheReconstructionProof
import YangMills.Construction.SystemsWithFiveBounds.BoundOnOneInsertedFieldAtNumbersProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.LimitTheorem.TranslationMeasureProof
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.ReconstructionComplements SpectralTheory
open OneLoopNotation (BddOp)
open ComplexHilbert (IsUnitaryMap)
open ProjectionMeasures (IsPVM)
open PVMCalculus
open HilbertSpaceBasics (ofBounded)
open ReflectionPositivity.Reconstruction (PhysicalSpace spanClass posClass spaceShift embedSpatial timeShift
  timeBasisVec)
open LimitTheorem.RotationsAndCone (spacelikeRegion isOpen_spacelikeRegion)
section Join
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
def spectralMeasureAsPVM (E : ProjectionMeasure 4 ℋ) : ProjectionMeasures.FourBorelSet → BddOp ℋ :=
  fun Δ => E Δ
theorem isPVM_spectralMeasureAsPVM
    (hWD : HilbertWellDefined.WellDefinedStatement) (E : ProjectionMeasure 4 ℋ) :
    IsPVM (spectralMeasureAsPVM E) where
  isProj Δ := by
    have hP := E.isStarProjection Δ
    refine ⟨(hWD.2.1 ℋ _).2 fun φ ψ => ?_, ?_⟩
    · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint φ ψ).symm
    · show E Δ = E Δ ^ 2
      rw [sq]
      exact hP.isIdempotentElem.eq.symm
  univ_eq := E.map_univ
  sigma_additive χ Δ hd := by
    have ht := E.tendsto_sum Δ hd χ
    have hc : Continuous fun v : ℋ => (⟪χ, v⟫_ℂ).re := by fun_prop
    have h₁ := (hc.tendsto _).comp ht
    have hre : ∀ A : BorelSets 4, ⟪χ, E A χ⟫_ℂ = ((‖E A χ‖ ^ 2 : ℝ) : ℂ) := fun A =>
      E.spectralValue_eq_norm_sq χ A
    have hre' : ∀ A : BorelSets 4, (⟪χ, E A χ⟫_ℂ).re = ‖E A χ‖ ^ 2 := fun A => by
      rw [hre, Complex.ofReal_re]
    have h₂ : Tendsto (fun N => ∑ r ∈ Finset.range N, ‖E (Δ r) χ‖ ^ 2) atTop
        (𝓝 (‖E ⟨⋃ r, (Δ r).1, MeasurableSet.iUnion fun r => (Δ r).2⟩ χ‖ ^ 2)) := by
      rw [← hre']
      refine h₁.congr fun N => ?_
      simp only [Function.comp_apply, inner_sum, Complex.re_sum]
      exact Finset.sum_congr rfl fun r _ => hre' _
    have hs := (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 h₂
    have hs' := Complex.hasSum_ofReal.2 hs
    show HasSum (fun k => ⟪χ, E (Δ k) χ⟫_ℂ) ⟪χ, E ⟨⋃ r, (Δ r).1, MeasurableSet.iUnion fun r => (Δ r).2⟩ χ⟫_ℂ
    rw [hre]
    simpa only [hre] using hs'
theorem hasMeasureDecomposition_spectralMeasureAsPVM
    (hCon : SpectralTheory.IntegralConstruction.IntegralConstructionHolds)
    (E : ProjectionMeasure 4 ℋ) (χ χ' : ℋ) :
    ProjectionMeasures.HasMeasureDecomposition
      (ProjectionMeasures.spectralScalarMeasure (spectralMeasureAsPVM E) χ χ')
      (fun k : Fin 4 => (1 / 4 : ℂ) * Complex.I ^ (k : ℕ))
      (fun k : Fin 4 => E.spectralValueMeasure (χ' + Complex.I ^ (k : ℕ) • χ)) where
  length_pos := by norm_num
  isFinite k := by
    refine ⟨?_⟩
    have e := E.spectralValueMeasure_apply (χ' + Complex.I ^ (k : ℕ) • χ) ⟨univ, MeasurableSet.univ⟩
    exact e.trans_lt ENNReal.ofReal_lt_top
  apply_eq Δ := by
    have h := (hCon 4 ℋ E).1.polarization χ χ' Δ
    show E.spectralPairing χ χ' Δ = _
    rw [h, Finset.sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [E.spectralValue_eq_spectralValueMeasure]
    ring
theorem hasWeakIntegrals_spectralMeasureAsPVM
    (hCon : SpectralTheory.IntegralConstruction.IntegralConstructionHolds)
    (hWD : HilbertWellDefined.WellDefinedStatement)
    (hRi : SpectralIntegralLawsHold) (E : ProjectionMeasure 4 ℋ)
    {u : (Fin 4 → ℝ) → ℂ} (hu : ProjectionMeasures.IsBddMeasurableFun u) :
    HasWeakIntegrals (spectralMeasureAsPVM E) u (E.boundedCalculus u) := by
  intro χ χ'
  have hb : IsBoundedComplexFn u := hu.2
  rw [(hRi 4 ℋ E).inner_boundedCalculus u hu.1 hb χ χ']
  have hw := hasMeasureDecomposition_spectralMeasureAsPVM hCon E χ χ'
  have hv := (hWD.2.2.1 _ u ⟨4, _, _, hw⟩ hu).2 _ ⟨4, _, _, hw, rfl⟩
  rw [← hv, ProjectionMeasure.polarizedIntegral, Finset.sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end Join
section Small
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
theorem compBounded_ofBounded (B C : ℋ →L[ℂ] ℋ) :
    compBounded (ofBounded B) C = ofBounded (B * C) := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.compBounded_ofBounded <;> assumption
theorem ofBounded_injective {A B : ℋ →L[ℂ] ℋ} (h : ofBounded A = ofBounded B) : A = B := by apply _root_.YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ofBounded_injective <;> assumption
theorem apply_eq_zero_of_subset (E : ProjectionMeasure 4 ℋ) {A B : BorelSets 4} (hAB : B.1 ⊆ A.1)
    (h0 : E A = 0) : E B = 0 := by
  have e := E.map_inter B A
  have hs : (⟨B.1 ∩ A.1, B.2.inter A.2⟩ : BorelSets 4) = B := Subtype.ext (Set.inter_eq_left.2 hAB)
  rw [hs, h0, mul_zero] at e
  exact e
end Small
theorem pushSpan_mem_spanIn {r : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (h : ∀ X ∈ supportedIn TimeAxis.upperHalfSpace, push r X ∈ supportedIn TimeAxis.upperHalfSpace)
    {C : FormalSpan} (hC : C ∈ spanIn TimeAxis.upperHalfSpace) :
    pushSpan r C ∈ spanIn TimeAxis.upperHalfSpace := by apply _root_.YangMills.SharedProofs.p30829 <;> assumption
theorem embedSpatial_eq_spacetimePoint (a : Fin 3 → ℝ) : embedSpatial a = Orthogonal.spacetimePoint a 0 := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.embedSpatial_eq_mkPoint <;> assumption
theorem spanClass_of_mem {σ : TupleFunctional} {h : HilbertSpaceBasics.IsPosSemidef (reflectionForm σ)}
    {G : FormalSpan} (hG : G ∈ spanIn TimeAxis.upperHalfSpace) :
    spanClass σ h G = posClass σ h ⟨G, hG⟩ := by apply _root_.YangMills.Construction.ReflectionPositivity.ReconstructionComplements.spanClass_of_mem <;> assumption
theorem pairing_evalOnMap (σ : TupleFunctional) :
    FieldFormConditions.pairing (evalOnMap σ) = reflectionForm σ := by apply _root_.YangMills.SharedProofs.p594 <;> assumption
open MinkowskiSpace in
theorem isBddMeasurableFun_kernel (t : ℝ) (ht : 0 ≤ t) (v : Fin 3 → ℝ) :
    ProjectionMeasures.IsBddMeasurableFun
      (closedFutureCone.indicator (TimeTranslations.laplaceFourierKernel t v)) := by
  have hcm : Continuous coneGap := by
    unfold coneGap spaceNorm spacePart
    fun_prop
  have hcl : MeasurableSet closedFutureCone :=
    (isClosed_le continuous_const hcm).measurableSet
  have hcd : Continuous (TimeTranslations.laplaceFourierKernel t v) := by
    unfold TimeTranslations.laplaceFourierKernel spacePart
    fun_prop
  refine ⟨hcd.measurable.indicator hcl, 1, fun p => ?_⟩
  by_cases hp : p ∈ closedFutureCone
  · rw [Set.indicator_of_mem hp, TimeTranslations.laplaceFourierKernel, Complex.norm_exp]
    have h0 : 0 ≤ p 0 := by
      have h₁ : 0 ≤ coneGap p := hp
      have h₂ : 0 ≤ spaceNorm (spacePart p) := Real.sqrt_nonneg _
      unfold coneGap at h₁
      linarith
    have e : (-(t : ℂ) * (p 0 : ℂ) + Complex.I * ((∑ i, v i * spacePart p i : ℝ) : ℂ)).re = -t * p 0 := by
      simp
    rw [e]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  · rw [Set.indicator_of_notMem hp]
    simp
theorem translationMeasureFromReconstruction_holds (hHF : HilbertSpaceFacts.Facts)
    (hFacts : BasicFacts.MainFacts)
    (hRules : OrthogonalAction.Laws.Statement) (hRi : SpectralIntegralLawsHold)
    (hGd : GeneratorsAndFlows.GeneratorFlowTheorem)
    (hCon : SpectralTheory.IntegralConstruction.IntegralConstructionHolds)
    (hWD : HilbertWellDefined.WellDefinedStatement)
    (hCal : BoundedFunctionalCalculus)
    (hCH : FormCompletion.FormCompletionIsHilbertSpace) (hSpec : TimeTranslations.MeasureAndFixedVectors) :
    TranslationMeasureFromReconstruction := by
  obtain ⟨-, -, -, -, -, hC, -, -, -, -, -, -, -, -, -, -, -, -, -, hId, -⟩ := hHF
  have hAct : BasicFacts.PushSpanProperties := hFacts.2.2.2.2.1
  intro σ h hfun hrec hcar hzero
  have hq := pairing_evalOnMap σ
  have hpos : FieldFormConditions.PairingPosSemidef (evalOnMap σ) := by
    unfold FieldFormConditions.PairingPosSemidef
    rw [hq]
    exact ⟨⟨h.add_left, h.smul_left, h.add_right, h.smul_right⟩, h.nonneg⟩
  refine ⟨hpos, ?_⟩
  have psh := (hWD.1 _ (FieldFormConditions.pairing (evalOnMap σ)) hpos).1
  obtain ⟨-, -, hMap⟩ := hCH _ (FieldFormConditions.pairing (evalOnMap σ)) psh
  have hnorm : ∀ F : PositiveSpan, ‖posClass σ h F‖ =
      FormCompletion.seminormOfForm (FieldFormConditions.pairing (evalOnMap σ)) F := fun F => by
    rw [@norm_eq_sqrt_re_inner ℂ, (hC _ (reflectionForm σ) h).2.1 F F, FormCompletion.seminormOfForm, hq]
    rfl
  obtain ⟨⟨B, hB, -⟩, hall⟩ := hMap (PhysicalSpace σ h) 1 (posClass σ h) zero_le_one fun F => by
    rw [one_mul, hnorm]
  obtain ⟨hBn, hBr⟩ := (hall B hB).2 hnorm
  have hdense : Dense (Set.range (posClass σ h)) := by
    have hd := (hC _ (reflectionForm σ) h).2.2.2.1
    rwa [LinearMap.coe_range] at hd
  have hV : IsUnitaryMap (B : FieldFormConditions.StateSpace (evalOnMap σ) →ₗ[ℂ] PhysicalSpace σ h) :=
    ⟨hBn, fun ψ => by
      have : ψ ∈ Set.range B := by
        rw [hBr, hdense.closure_eq]
        exact Set.mem_univ _
      exact this⟩
  set E := jointMeasure σ h with hE
  have hP := isPVM_spectralMeasureAsPVM hWD E
  have hcarry : ProjectionMeasures.IsSupportedOn (spectralMeasureAsPVM E)
      ProjectionMeasures.FourBorelSet.univ := by
    show E ⟨Set.univᶜ, _⟩ = 0
    have : (⟨Set.univᶜ, MeasurableSet.univ.compl⟩ : BorelSets 4) = ⟨∅, MeasurableSet.empty⟩ :=
      Subtype.ext Set.compl_univ
    rw [this]
    exact E.map_empty
  obtain ⟨-, hI, -, -, -, hConj, -⟩ := (hCal.2 (PhysicalSpace σ h)).2 (spectralMeasureAsPVM E) _ hP hcarry
  have hConjV := hConj _ _ hV
  have hIntEq : ∀ u, ProjectionMeasures.IsBddMeasurableFun u →
      pvmIntegral (spectralMeasureAsPVM E) u = E.boundedCalculus u := fun u hu =>
    ((hI.1 u hu).2.1 _ (hasWeakIntegrals_spectralMeasureAsPVM hCon hWD hRi E hu)).symm
  have RE := hRi 4 (PhysicalSpace σ h) E
  have hbelow : unitaryConj hV (spectralMeasureAsPVM E TimeTranslations.subConeSet) = 0 := by
    have e : TimeTranslations.subConeSet = ⟨spacelikeRegion, isOpen_spacelikeRegion.measurableSet⟩ := by
      refine Subtype.ext (Set.ext fun p => ?_)
      show p 0 < Real.sqrt (∑ i : Fin 3, p i.succ ^ 2) ↔ p 0 < Real.sqrt (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)
      rw [Fin.sum_univ_three]
      rfl
    have e₂ : spectralMeasureAsPVM E TimeTranslations.subConeSet = 0 := by
      rw [e]
      exact hzero
    rw [e₂]
    ext ψ
    simp [PVMCalculus.unitaryConj]
  obtain ⟨-, hT, -, -, -, ⟨F₁, hF₁, hF₁c, hF₁e⟩, -, -⟩ := hrec.2.1
  obtain ⟨-, hS, -, -, -, -, -⟩ := hrec.2.2.1
  obtain ⟨-, F₂, hF₂, -, hF₂m⟩ := hcar
  have hFF : F₁ = F₂ :=
    ((hGd (PhysicalSpace σ h)).1 F₂).2.2.1.eq_of_generator F₁ (hF₁.symm.trans hF₂)
  subst hFF
  have hdict : TimeTranslations.IntertwinesShifts (evalOnMap σ)
      (fun Δ => unitaryConj hV (spectralMeasureAsPVM E Δ)) := by
    intro F t v ht
    have hu := isBddMeasurableFun_kernel t ht v
    set u := MinkowskiSpace.closedFutureCone.indicator (TimeTranslations.laplaceFourierKernel t v) with hudef
    rw [hConjV.2.2 u hu, hIntEq u hu]
    have hBU : E.boundedCalculus u = timeShift σ h ⟨t, ht⟩ * spaceShift σ h v := by
      have hm := (congrArg (fun A => compBounded A (spaceShift σ h v)) (hF₁e ⟨t, ht⟩)).trans
        (hF₂m ⟨t, ht⟩ v)
      simp only [compBounded_ofBounded] at hm
      have hcm : Continuous (heatPhase ⟨t, ht⟩ v) := by
        unfold heatPhase spatialPart LimitConventions.spaceDot SeparatedTupleFunctionals.dotProd
        fun_prop
      have hnull : E ⟨{x | u x ≠ heatPhase ⟨t, ht⟩ v x}, (measurableSet_eq_fun hu.1 hcm.measurable).compl⟩ = 0 := by
        refine apply_eq_zero_of_subset E (A := ⟨spacelikeRegion, isOpen_spacelikeRegion.measurableSet⟩) ?_ hzero
        intro x hx
        by_contra hnb
        have hle : Real.sqrt (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) ≤ x 0 := not_lt.1 hnb
        have hcone : x ∈ MinkowskiSpace.closedFutureCone := by
          show 0 ≤ x 0 - Real.sqrt (∑ i : Fin 3, x i.succ ^ 2)
          rw [Fin.sum_univ_three]
          exact sub_nonneg.2 hle
        apply hx
        rw [hudef, Set.indicator_of_mem hcone]
        simp only [TimeTranslations.laplaceFourierKernel, heatPhase, MinkowskiSpace.spacePart, spatialPart,
          LimitConventions.spaceDot, SeparatedTupleFunctionals.dotProd]
        push_cast
        rfl
      have e₁ := RE.calculus_congr u _ hu.1 hcm.measurable hnull
      have e₂ : E.functionalCalculus u = toUnboundedOperator (E.boundedCalculus u) :=
        RE.isBoundedCalculusOf u hu.1 hu.2
      exact ofBounded_injective (e₂.symm.trans (e₁.trans hm.symm))
    have hG : pushSpan (translate (embedSpatial v)) F.1 ∈ spanIn TimeAxis.upperHalfSpace :=
      pushSpan_mem_spanIn (fun X hX => by
        rw [embedSpatial_eq_spacetimePoint]
        exact ((hRules.2.2.1 1).2.1 X hX).2 v) F.2
    have hG₂ : pushSpan (translate (t • timeBasisVec)) (pushSpan (translate (embedSpatial v)) F.1) ∈
        spanIn TimeAxis.upperHalfSpace :=
      pushSpan_mem_spanIn (fun X hX => ((hRules.2.2.1 1).2.1 X hX).1 t ht) hG
    have hsum : pushSpan (translate (t • timeBasisVec)) (pushSpan (translate (embedSpatial v)) F.1) =
        pushSpan (translate (TimeTranslations.timeSpaceVec t v)) F.1 :=
      (hAct _ _ (isEuclidIsometry_translate 0) (isEuclidIsometry_translate 0) _ _ F.1).2.1
    have hA : E.boundedCalculus u (posClass σ h F) =
        posClass σ h (ReflectionPositivity.FormProperties.shiftedSpan (TimeTranslations.timeSpaceVec t v) F) := by
      rw [hBU]
      show timeShift σ h ⟨t, ht⟩ (spaceShift σ h v (posClass σ h F)) = _
      rw [hS v F, spanClass_of_mem hG, hT ⟨t, ht⟩ ⟨_, hG⟩]
      refine (spanClass_of_mem hG₂).trans ?_
      unfold ReflectionPositivity.FormProperties.shiftedSpan
      rw [dif_pos (hsum ▸ hG₂)]
      exact congrArg _ (Subtype.ext hsum)
    have hcl : ∀ G : PositiveSpan, B (FieldFormConditions.stateOf (evalOnMap σ) G) = posClass σ h G := hB
    show (unitaryIsometry hV).symm (E.boundedCalculus u (unitaryIsometry hV _)) = _
    have h₁ : unitaryIsometry hV (FieldFormConditions.stateOf (evalOnMap σ) F) = posClass σ h F := hcl F
    rw [h₁, hA, LinearIsometryEquiv.symm_apply_eq]
    exact (hcl _).symm
  exact ⟨_, (hSpec _ hfun hpos).1 _ hConjV.1 hbelow hdict⟩
end YangMills.Construction.LimitTheorem.TranslationMeasureProof
end
