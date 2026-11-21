import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStates
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsGaugeInvarianceAndCompactness
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GibbsCharacterization
variable {a : ℝ}
theorem measurable_eval_link (b : Link a) : Measurable fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval <;> assumption
theorem linkSigma_le (S : Set (Link a)) :
    linkSigma S ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.SymmetryActionProof.linkSigma_le_borel <;> assumption
theorem comap_eval_le_comap_eval_opposite (b : Link a) :
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance ≤
      MeasurableSpace.comap (fun U : GaugeField a => U b.opposite) inferInstance := by
  rintro _ ⟨O, hO, rfl⟩
  refine ⟨(fun g : Matrices.ComplexMatrix2.specialUnitary => g⁻¹) ⁻¹' O,
    continuous_inv.measurable hO, ?_⟩
  ext U
  simp only [mem_preimage]
  rw [U.2 b, inv_inv]
theorem opposite_isPositivelyOriented_of_not {b : Link a} (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem exteriorSigma_eq (ha : 0 < a) (W : LinkWindow a) :
    exteriorSigma W.links = W.exteriorSigma := by
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    by_cases hp : b.IsPositivelyOriented
    · exact le_iSup₂_of_le (f := fun (c : Link a)
        (_ : c ∈ {c : Link a | c.IsPositivelyOriented ∧ c ∉ W.links}) =>
        MeasurableSpace.comap (fun U : GaugeField a => U c) inferInstance) b ⟨hp, hb.1⟩ le_rfl
    · exact (comap_eval_le_comap_eval_opposite b).trans
        (le_iSup₂_of_le (f := fun (c : Link a)
          (_ : c ∈ {c : Link a | c.IsPositivelyOriented ∧ c ∉ W.links}) =>
          MeasurableSpace.comap (fun U : GaugeField a => U c) inferInstance) b.opposite
          ⟨opposite_isPositivelyOriented_of_not hp, hb.2⟩ le_rfl)
  · refine iSup₂_le fun b hb => ?_
    exact le_iSup₂_of_le (f := fun (c : Link a)
        (_ : c ∈ {c : Link a | c ∉ W.links ∧ c.opposite ∉ W.links}) =>
        MeasurableSpace.comap (fun U : GaugeField a => U c) inferInstance) b
      ⟨hb.2, fun h => Link.opposite_not_isPositivelyOriented ha hb.1 (W.isPositive _ h)⟩ le_rfl
theorem glue_apply (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (U : GaugeField a)
    (b : Link a) :
    W.glue ha V U b = open Classical in if h : b ∈ W.links then V ⟨b, h⟩ else
      if h' : b.opposite ∈ W.links then (V ⟨b.opposite, h'⟩)⁻¹ else U b := rfl
theorem patch_eq_glue (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (U : GaugeField a)
    {b : Link a} (hb : b.IsPositivelyOriented) : patch W.links V U b = W.glue ha V U b := by
  have hr : b.opposite ∉ W.links := fun h =>
    Link.opposite_not_isPositivelyOriented ha hb (W.isPositive _ h)
  rw [glue_apply]
  by_cases h : b ∈ W.links
  · simp [patch, h]
  · simp [patch, h, hr]
theorem faceEnergy_patch (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (U : GaugeField a)
    (p : ElementaryPlaquette a) :
    faceEnergy (patch W.links V U) p = faceEnergy (W.glue ha V U) p := by
  have hf : ∀ (x : LatticePoint a) (μ : Fin 4), patch W.links V U (Link.forwardFrom x μ) =
      W.glue ha V U (Link.forwardFrom x μ) := fun x μ =>
    patch_eq_glue ha W V U ⟨μ, by simp [Link.forwardFrom]⟩
  simp only [faceEnergy, faceHolonomy, hf]
theorem boltzmannWeight_eq (ha : 0 < a) (β : ℝ) (W : LinkWindow a) (V : W.Assignments)
    (U : GaugeField a) :
    boltzmannWeight β W.links U V = W.localWeight β (W.glue ha V U) := by
  simp only [boltzmannWeight, LinkWindow.localWeight, faceEnergy_patch ha]
  rfl
theorem restrictTo_glue (ha : 0 < a) (W : LinkWindow a) (V : W.Assignments) (U : GaugeField a) :
    restrictTo W.links (W.glue ha V U) = V := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.restrictTo_glue <;> assumption
theorem isBoundedObservable_indicator {E : Set (GaugeField a)} (hE : MeasurableSet E) :
    IsBoundedObservable (E.indicator (1 : GaugeField a → ℂ)) := by
  refine ⟨measurable_one.indicator hE, 1, fun U => ?_⟩
  by_cases h : U ∈ E <;> simp [h]
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : Integrable F ν := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem measurable_restrictTo (S : Finset (Link a)) : Measurable (restrictTo S) :=
  measurable_pi_lambda _ fun b => measurable_eval_link b.1
theorem conditionalExpectation_indicator {ha : 0 < a} {β : ℝ}
    (hs : SpecificationProperties ha β) (W : LinkWindow a)
    {A : Set (W.links → Matrices.ComplexMatrix2.specialUnitary)} (hA : MeasurableSet A)
    (U : GaugeField a) :
    W.conditionalExpectation ha β ((restrictTo W.links ⁻¹' A).indicator 1) U =
      ((wilsonSpecification β W.links U A).toReal : ℂ) := by
  have hE : MeasurableSet (restrictTo W.links ⁻¹' A) := measurable_restrictTo _ hA
  obtain ⟨-, hw, hZ⟩ := ((hs W).1 _ (isBoundedObservable_indicator hE) U).1
  set w : W.Assignments → ℝ := fun V => W.localWeight β (W.glue ha V U) with hwdef
  have hwpos : ∀ V, 0 ≤ w V := fun V => (Real.exp_pos _).le
  have hZ' : partitionFunction β W.links U = ∫ V, w V ∂W.haarProd := by
    unfold partitionFunction
    exact integral_congr_ae (Filter.Eventually.of_forall fun V => boltzmannWeight_eq ha β W V U)
  have hZpos : 0 < ∫ V, w V ∂W.haarProd :=
    lt_of_le_of_ne (integral_nonneg hwpos) (Ne.symm hZ)
  have hnum : (∫ V, ((restrictTo W.links ⁻¹' A).indicator (1 : GaugeField a → ℂ))
      (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ) ∂W.haarProd) =
      ((∫ V in A, w V ∂W.haarProd : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    by_cases hV : V ∈ A
    · have : W.glue ha V U ∈ restrictTo W.links ⁻¹' A := by
        rw [mem_preimage, restrictTo_glue]
        exact hV
      simp [hV, this, hwdef]
    · have : W.glue ha V U ∉ restrictTo W.links ⁻¹' A := by
        rw [mem_preimage, restrictTo_glue]
        exact hV
      simp [hV, this]
  have hmass : (wilsonSpecification β W.links U A).toReal =
      (∫ V in A, w V ∂W.haarProd) / ∫ V, w V ∂W.haarProd := by
    have hdens : (fun v : W.links → Matrices.ComplexMatrix2.specialUnitary =>
        ENNReal.ofReal (boltzmannWeight β W.links U v)) = fun v => ENNReal.ofReal (w v) := by
      funext v
      rw [boltzmannWeight_eq ha]
    have hlint : ∫⁻ v in A, ENNReal.ofReal (w v) ∂W.haarProd =
        ENNReal.ofReal (∫ V in A, w V ∂W.haarProd) :=
      (ofReal_integral_eq_lintegral_ofReal hw.integrableOn
        (Filter.Eventually.of_forall hwpos)).symm
    have happly : wilsonSpecification β W.links U A =
        (ENNReal.ofReal (∫ V, w V ∂W.haarProd))⁻¹ *
          ENNReal.ofReal (∫ V in A, w V ∂W.haarProd) := by
      unfold wilsonSpecification
      rw [Measure.smul_apply, hdens, withDensity_apply _ hA, hZ', smul_eq_mul]
      exact congrArg _ hlint
    rw [happly, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZpos.le,
      ENNReal.toReal_ofReal (integral_nonneg fun V => hwpos V), div_eq_inv_mul]
  unfold LinkWindow.conditionalExpectation
  rw [hnum, hmass]
  push_cast
  rfl
theorem integral_indicator_mul_conditionalExpectation {ha : 0 < a} {β : ℝ}
    (hs : SpecificationProperties ha β) (W : LinkWindow a)
    {A : Set (W.links → Matrices.ComplexMatrix2.specialUnitary)}
    (hA : MeasurableSet A) (ν : Measure (GaugeField a)) {S : Set (GaugeField a)}
    (hS : MeasurableSet S) :
    ∫ U, S.indicator (1 : GaugeField a → ℂ) U *
        W.conditionalExpectation ha β ((restrictTo W.links ⁻¹' A).indicator 1) U ∂ν =
      ((∫ U in S, (wilsonSpecification β W.links U A).toReal ∂ν : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal, ← integral_indicator hS]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  beta_reduce
  rw [conditionalExpectation_indicator hs W hA U]
  by_cases hU : U ∈ S <;> simp [hU]
theorem isGibbs_of_mem_gibbsClass {ha : 0 < a} {β : ℝ}
    (hs : SpecificationProperties ha β)
    (hc : ∀ W : LinkWindow a, KernelIsConditionalExpectation ha β W)
    {ν : Measure (GaugeField a)} (hν : ν ∈ gibbsClass ha β) : IsGibbs β ν := by
  have hprob : IsProbabilityMeasure ν := hν.1
  refine ⟨hprob, fun Λ hpos B hB => ?_⟩
  let W : LinkWindow a := ⟨Λ, hpos⟩
  have hB' : MeasurableSet (show Set (W.links → Matrices.ComplexMatrix2.specialUnitary) from B) :=
    hB
  have hE : MeasurableSet (restrictTo Λ ⁻¹' B) := measurable_restrictTo _ hB
  have hm : exteriorSigma Λ ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    linkSigma_le _
  have hσ : exteriorSigma Λ = W.exteriorSigma := exteriorSigma_eq ha W
  set F : GaugeField a → ℂ := (restrictTo Λ ⁻¹' B).indicator 1 with hFdef
  have hF : IsBoundedObservable F := isBoundedObservable_indicator hE
  have hγ := hc W F hF
  have hval : ∀ U, W.conditionalExpectation ha β F U =
      ((wilsonSpecification β Λ U B).toReal : ℂ) :=
    fun U => conditionalExpectation_indicator hs W hB' U
  have hre : (fun U => (wilsonSpecification β Λ U B).toReal) =
      fun U => (W.conditionalExpectation ha β F U).re := by
    funext U
    rw [hval]
    simp
  have hobs := ((hs W).2.2.2.2.2.2.1 F hF).1
  have hint : Integrable (fun U => (wilsonSpecification β Λ U B).toReal) ν := by
    rw [hre]
    exact (integrable_of_isBoundedObservable ν hobs).re
  have hmeas : Measurable[exteriorSigma Λ] fun U => (wilsonSpecification β Λ U B).toReal := by
    rw [hre, hσ]
    exact Complex.measurable_re.comp hγ.1
  refine ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hE)
    (fun s _ _ => hint.integrableOn) (fun s hs' _ => ?_)
    hmeas.stronglyMeasurable.aestronglyMeasurable
  have hsW : MeasurableSet[W.exteriorSigma] s := hσ ▸ hs'
  have hsm : MeasurableSet s := hm _ hs'
  have hH : Measurable[W.exteriorSigma] (s.indicator (1 : GaugeField a → ℂ)) :=
    (@measurable_one _ _ _ W.exteriorSigma _).indicator hsW
  have hbound : ∃ C : ℝ, ∀ U, ‖s.indicator (1 : GaugeField a → ℂ) U‖ ≤ C :=
    ⟨1, fun U => by by_cases h : U ∈ s <;> simp [h]⟩
  have key := (hγ.2 ν hν).1 _ hH hbound
  rw [integral_indicator_mul_conditionalExpectation hs W hB' ν hsm] at key
  have hright : ∫ U, s.indicator (1 : GaugeField a → ℂ) U * F U ∂ν =
      ((∫ U in s, (restrictTo Λ ⁻¹' B).indicator (fun _ => (1 : ℝ)) U ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator hsm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    by_cases h1 : U ∈ s <;> by_cases h2 : U ∈ restrictTo Λ ⁻¹' B <;> simp [hFdef, h1, h2]
  rw [hright] at key
  exact_mod_cast key
theorem integral_conditionalExpectation_of_isGibbs {ha : 0 < a} {β : ℝ}
    (hs : SpecificationProperties ha β)
    (hborel : (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a)))
    {ν : Measure (GaugeField a)} (hν : IsGibbs β ν) (W : LinkWindow a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν := by
  have hprob : IsProbabilityMeasure ν := hν.1
  obtain ⟨ν', hprob', hmass, hint⟩ := (hs W).2.2.2.2.2.2.2.2.2.2 ν hprob
  have hσ : exteriorSigma W.links = W.exteriorSigma := exteriorSigma_eq ha W
  have hout : W.exteriorSigma ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    linkSigma_le _
  let C : Set (Set (GaugeField a)) :=
    {E | ∃ A : Set (W.links → Matrices.ComplexMatrix2.specialUnitary), MeasurableSet A ∧
      ∃ S : Set (GaugeField a), MeasurableSet[W.exteriorSigma] S ∧
        E = restrictTo W.links ⁻¹' A ∩ S}
  have hC : ∀ E ∈ C, MeasurableSet E := by
    rintro _ ⟨A, hA, S, hS, rfl⟩
    exact (measurable_restrictTo _ hA).inter (hout _ hS)
  have hpi : IsPiSystem C := by
    rintro _ ⟨A, hA, S, hS, rfl⟩ _ ⟨A', hA', S', hS', rfl⟩ -
    refine ⟨A ∩ A', hA.inter hA', S ∩ S', MeasurableSet.inter hS hS', ?_⟩
    ext U
    simp only [mem_inter_iff, mem_preimage]
    tauto
  have hpos : ∀ b : Link a, b.IsPositivelyOriented →
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance ≤
        MeasurableSpace.generateFrom C := by
    rintro b hb _ ⟨O, hO, rfl⟩
    apply MeasurableSpace.measurableSet_generateFrom
    by_cases h : b ∈ W.links
    · refine ⟨(fun v : W.links → Matrices.ComplexMatrix2.specialUnitary => v ⟨b, h⟩) ⁻¹' O,
        measurable_pi_apply _ hO, univ, MeasurableSet.univ, ?_⟩
      ext U
      simp [restrictTo]
    · refine ⟨univ, MeasurableSet.univ, (fun U : GaugeField a => U b) ⁻¹' O, ?_, ?_⟩
      · have hle : MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance ≤
            W.exteriorSigma :=
          le_iSup₂_of_le (f := fun (c : Link a)
            (_ : c ∈ {c : Link a | c.IsPositivelyOriented ∧ c ∉ W.links}) =>
            MeasurableSpace.comap (fun U : GaugeField a => U c) inferInstance) b ⟨hb, h⟩ le_rfl
        exact hle _ ⟨O, hO, rfl⟩
      · simp
  have hgen : (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [hborel]
      refine iSup₂_le fun b _ => ?_
      by_cases hp : b.IsPositivelyOriented
      · exact hpos b hp
      · exact (comap_eval_le_comap_eval_opposite b).trans
          (hpos _ (opposite_isPositivelyOriented_of_not hp))
    · exact MeasurableSpace.generateFrom_le hC
  have hagree : ∀ E ∈ C, ν' E = ν E := by
    rintro _ ⟨A, hA, S, hS, rfl⟩
    have hSm : MeasurableSet S := hout _ hS
    have hEA : MeasurableSet (restrictTo W.links ⁻¹' A) := measurable_restrictTo _ hA
    have hE : MeasurableSet (restrictTo W.links ⁻¹' A ∩ S) := hEA.inter hSm
    have hFA := isBoundedObservable_indicator hEA
    have hH : Measurable[W.exteriorSigma] (S.indicator (1 : GaugeField a → ℂ)) :=
      (@measurable_one _ _ _ W.exteriorSigma _).indicator hS
    have hHobs : IsBoundedObservable (S.indicator (1 : GaugeField a → ℂ)) :=
      isBoundedObservable_indicator hSm
    have hprod : (restrictTo W.links ⁻¹' A ∩ S).indicator (1 : GaugeField a → ℂ) =
        (restrictTo W.links ⁻¹' A).indicator 1 * S.indicator 1 := by
      funext U
      by_cases h1 : U ∈ restrictTo W.links ⁻¹' A <;> by_cases h2 : U ∈ S <;> simp [h1, h2]
    have h1 := hmass _ hE
    rw [hprod, stateEval, (hs W).2.2.2.2.2.2.2.1 _ _ hFA hHobs hH] at h1
    change _ = ∫ U, S.indicator (1 : GaugeField a → ℂ) U *
      W.conditionalExpectation ha β ((restrictTo W.links ⁻¹' A).indicator 1) U ∂ν at h1
    rw [integral_indicator_mul_conditionalExpectation hs W hA ν hSm] at h1
    have h2 : (ν' (restrictTo W.links ⁻¹' A ∩ S)).toReal =
        ∫ U in S, (wilsonSpecification β W.links U A).toReal ∂ν := by exact_mod_cast h1
    have hm : exteriorSigma W.links ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
      linkSigma_le _
    have hSσ : MeasurableSet[exteriorSigma W.links] S := hσ ▸ hS
    have hae := hν.2 W.links W.isPositive A hA
    have h3 : ∫ U in S, (wilsonSpecification β W.links U A).toReal ∂ν =
        ∫ U in S, (restrictTo W.links ⁻¹' A).indicator (fun _ => (1 : ℝ)) U ∂ν := by
      rw [integral_congr_ae (ae_restrict_of_ae hae)]
      exact setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hEA) hSσ
    have h4 : ∫ U in S, (restrictTo W.links ⁻¹' A).indicator (fun _ => (1 : ℝ)) U ∂ν =
        (ν (restrictTo W.links ⁻¹' A ∩ S)).toReal := by
      rw [setIntegral_indicator hEA, inter_comm]
      simp [Measure.real]
    rw [h3, h4] at h2
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h2
  have heq : ν' = ν :=
    ext_of_generate_finite C hgen hpi hagree (by simp)
  have hfin := hint F hF
  rw [heq] at hfin
  exact hfin.symm
theorem tfae_gibbs
    (hs : ∀ {a : ℝ} (ha : 0 < a) (β : ℝ), 0 < β → SpecificationProperties ha β)
    (hc : ∀ {a : ℝ} (ha : 0 < a) (β : ℝ), 0 < β → ∀ W : LinkWindow a,
      KernelIsConditionalExpectation ha β W)
    (hborel : ∀ a : ℝ, 0 < a → (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a)))
    (a : ℝ) (ha : 0 < a) (β : ℝ) (hβ : 0 < β) (ν : Measure (GaugeField a))
    (hν : IsProbabilityMeasure ν) :
    List.TFAE
      [ν ∈ gibbsClass ha β,
        ∀ W : LinkWindow a, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
          ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν,
        IsGibbs β ν] := by
  tfae_have 1 → 2 := fun h W F hF => ((hc ha β hβ W F hF).2 ν h).2.2
  tfae_have 2 → 1 := fun h => ⟨hν, fun W F hF => h W F hF.1⟩
  tfae_have 1 → 3 := isGibbs_of_mem_gibbsClass (hs ha β hβ) (hc ha β hβ)
  tfae_have 3 → 2 := fun h W F hF =>
    integral_conditionalExpectation_of_isGibbs (hs ha β hβ) (hborel a ha) h W hF
  tfae_finish
theorem gibbsClassEqGibbsStates_of (hElem : ElementaryLatticeFacts)
    (hEq : GibbsClassStructure)
    (hSpace : FieldSpace.SymmetryProperties) :
    GibbsClassEqGibbsStates := by
  have hs : ∀ {a : ℝ} (ha : 0 < a) (β : ℝ), 0 < β → SpecificationProperties ha β :=
    fun {a} ha β hβ => (hElem a β ha hβ).2.2.1
  have hc : ∀ {a : ℝ} (ha : 0 < a) (β : ℝ), 0 < β → ∀ W : LinkWindow a,
      KernelIsConditionalExpectation ha β W :=
    fun {a} ha β hβ => (hEq a ha β hβ).1
  have hborel : ∀ a : ℝ, 0 < a → (inferInstance : MeasurableSpace (GaugeField a)) =
      linkSigma (univ : Set (Link a)) := fun a ha => (hSpace a ha).1.2.2
  have hform := tfae_gibbs hs hc hborel
  have hclass : ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β →
      gibbsClass ha β = {ν | IsGibbs β ν} := by
    intro a ha β hβ
    ext ν
    constructor
    · intro h
      exact (hform a ha β hβ ν h.1).out 0 2 |>.mp h
    · intro h
      exact (hform a ha β hβ ν h.1).out 0 2 |>.mpr h
  have hper : ∀ (a : ℝ) (ha : 0 < a) (β : ℝ), 0 < β →
      periodicGibbsClass ha β = {ν | IsPeriodicGibbs β ν} := by
    intro a ha β hβ
    ext ν
    simp only [periodicGibbsClass, subgroupInvariantGibbsClass, mem_iUnion, mem_ofPred_eq,
      hclass a ha β hβ, IsPeriodicGibbs, IsPeriodicMeasure, exists_prop]
    constructor
    · rintro ⟨Q, hQ, hg, hi⟩
      exact ⟨hg, Q, hQ, hi⟩
    · rintro ⟨hg, Q, hQ, hi⟩
      exact ⟨Q, hQ, hg, hi⟩
  refine ⟨hform, fun a ha β hβ => ⟨hclass a ha β hβ, hper a ha β hβ⟩, ?_⟩
  intro L _ _ J ha β hβ
  exact hper _ ha β hβ
end YangMills.Construction.InfiniteLattice.GibbsCharacterization
