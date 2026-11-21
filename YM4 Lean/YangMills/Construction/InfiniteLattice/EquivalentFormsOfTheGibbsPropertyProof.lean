import YangMills.Construction.InfiniteLattice.ContinuousObservablesAndTheWilsonKernelOfACutoff
import YangMills.Construction.InfiniteLattice.CountableProductsOfCopiesOfTheGroup
import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStates
import YangMills.Construction.InfiniteLattice.FactsOfTheSpecificationAtEverySpacing
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GibbsEquivalences
open MeasureTheory Set
open YangMills.Construction.GibbsAtFixedSpacing
variable {a : ℝ}
def linkWindowOfFinset (𝓛 : Finset (Link a)) (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) :
    LinkWindow a :=
  ⟨𝓛, fun _ hb => mem_positiveLinks_iff.1 (h𝓛 hb)⟩
theorem links_subset_positiveLinks (W : LinkWindow a) :
    (W.links : Set (Link a)) ⊆ positiveLinkSet a :=
  fun b hb => mem_positiveLinks_iff.2 (W.isPositive b hb)
theorem overwriteLinks_eq_glue (ha : 0 < a) (W : LinkWindow a)
    (h : HasNoOppositePairs (W.links : Set (Link a)))
    (V : LinkVariables (W.links : Set (Link a))) (U : GaugeField a) :
    overwriteLinks h V U = W.glue ha V U := by
  apply Subtype.ext
  funext b
  by_cases hin : b ∈ W.links
  · have lhs : overwriteLinks h V U b = V ⟨b, hin⟩ := dif_pos (Finset.mem_coe.2 hin)
    have rhs : W.glue ha V U b = V ⟨b, hin⟩ := dif_pos hin
    exact lhs.trans rhs.symm
  · by_cases hop : b.opposite ∈ W.links
    · have lhs : overwriteLinks h V U b = (V ⟨b.opposite, hop⟩)⁻¹ :=
        (dif_neg (mt Finset.mem_coe.1 hin)).trans (dif_pos (Finset.mem_coe.2 hop))
      have rhs : W.glue ha V U b = (V ⟨b.opposite, hop⟩)⁻¹ := (dif_neg hin).trans (dif_pos hop)
      exact lhs.trans rhs.symm
    · have lhs : overwriteLinks h V U b = U b :=
        (dif_neg (mt Finset.mem_coe.1 hin)).trans (dif_neg (mt Finset.mem_coe.1 hop))
      have rhs : W.glue ha V U b = U b := (dif_neg hin).trans (dif_neg hop)
      exact lhs.trans rhs.symm
theorem glueOnLinks_eq_splice (ha : 0 < a) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a)
    (V : 𝓛 → Matrices.ComplexMatrix2.specialUnitary) :
    glueOnLinks ha 𝓛 h𝓛 U V = WilsonOperator.splice ha h𝓛 V U := by
  refine WilsonOperator.eq_splice ha h𝓛 V U _ (fun b => ?_) (fun b hb => ?_)
  · exact overwriteLinks_apply_of_mem (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) _ U ⟨b.1, b.2⟩
  · exact overwriteLinks_apply_of_not_mem (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) _ U hb.2
      (fun hr => opposite_notMem_positiveLinks ha hb.1 (h𝓛 hr))
theorem plaquettesTouching_eq_facesTouching (ha : 0 < a) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) :
    plaquettesTouching 𝓛 = facesTouching 𝓛 := by apply _root_.YangMills.Construction.InfiniteLattice.CutoffStates.plaquettesTouching_eq_facesTouching <;> assumption
theorem specKernel_eq_conditionalExpectation (ha : 0 < a) (β : ℝ) (W : LinkWindow a)
    (h𝓛 : (W.links : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ) :
    specKernel ha β W.links h𝓛 F = W.conditionalExpectation ha β F := by
  funext U
  have hw : ∀ U' : GaugeField a, Real.exp (-wilsonLinkEnergy β W.links U') =
      W.localWeight β U' := fun U' => by
    simp only [wilsonLinkEnergy, LinkWindow.localWeight,
      plaquettesTouching_eq_facesTouching ha W.links h𝓛, neg_mul]
    rfl
  simp only [specKernel, wilsonLinkKernel, linkKernel, LinkWindow.conditionalExpectation,
    hw, overwriteLinks_eq_glue ha W]
  rfl
theorem isBoundedObservable_mul {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    IsBoundedObservable fun U => F U * H U := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.isBoundedObservable_mul <;> assumption
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : Integrable F ν := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem isProbabilityMeasure_haarPi (ι : Type) [Countable ι] :
    IsProbabilityMeasure (Matrices.ComplexMatrix2.haarPi ι) := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.isProbabilityMeasure_haarPi <;> assumption
theorem integrable_boltzmannWeight (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a) :
    Integrable (boltzmannWeight β 𝓛 U) (Matrices.ComplexMatrix2.haarPi 𝓛) := by
  have := WilsonOperator.secondCountable_specialUnitary
  have := isProbabilityMeasure_haarPi 𝓛
  exact (WilsonOperator.continuous_boltzmannWeight (Λ := 𝓛) β U).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
theorem partitionFunction_pos (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a) :
    0 < partitionFunction β 𝓛 U :=
  have := isProbabilityMeasure_haarPi 𝓛
  integral_exp_pos (integrable_boltzmannWeight β 𝓛 U)
theorem isProbabilityMeasure_wilsonSpecification (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a) :
    IsProbabilityMeasure (wilsonSpecification β 𝓛 U) := by
  refine ⟨?_⟩
  have hZ := partitionFunction_pos β 𝓛 U
  have hl : ∫⁻ v, ENNReal.ofReal (boltzmannWeight β 𝓛 U v) ∂Matrices.ComplexMatrix2.haarPi 𝓛 =
      ENNReal.ofReal (partitionFunction β 𝓛 U) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_boltzmannWeight β 𝓛 U)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  unfold wilsonSpecification
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hl,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top
theorem continuous_glueOnLinks (ha : 0 < a) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    Continuous (glueOnLinks ha 𝓛 h𝓛 U) :=
  OrientedLinkSet.continuous_glue
    ⟨𝓛, hasNoOppositePairs_of_subset_positiveLinks ha h𝓛⟩ U
theorem measurable_glueOnLinks (ha : 0 < a) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) (U : GaugeField a) :
    Measurable (glueOnLinks ha 𝓛 h𝓛 U) := by
  have := WilsonOperator.secondCountable_specialUnitary
  exact (continuous_glueOnLinks ha 𝓛 h𝓛 U).measurable
theorem glue_eq_splice (ha : 0 < a) (W : LinkWindow a)
    (h𝓛 : (W.links : Set (Link a)) ⊆ positiveLinkSet a) (V : W.Assignments)
    (U : GaugeField a) : W.glue ha V U = WilsonOperator.splice ha h𝓛 V U :=
  (overwriteLinks_eq_glue ha W (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) V U).symm.trans
    (glueOnLinks_eq_splice ha W.links h𝓛 U V)
theorem specKernel_eq_kernelOperator (ha : 0 < a) (β : ℝ) (W : LinkWindow a)
    (h𝓛 : (W.links : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ)
    (U : GaugeField a) :
    specKernel ha β W.links h𝓛 F U = WilsonOperator.kernelOperator ha β h𝓛 F U := by
  rw [specKernel_eq_conditionalExpectation ha β W h𝓛 F]
  unfold LinkWindow.conditionalExpectation WilsonOperator.kernelOperator WilsonOperator.localPartition
  simp only [glue_eq_splice ha W h𝓛]
  rw [div_eq_inv_mul]
  rfl
theorem specKernel_eq_integral (ha : 0 < a) (β : ℝ) (𝓛 : Finset (Link a))
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) (F : GaugeField a → ℂ)
    (U : GaugeField a) :
    specKernel ha β 𝓛 h𝓛 F U =
      ∫ V, F (glueOnLinks ha 𝓛 h𝓛 U V)
        ∂wilsonSpecificationAt ha β 𝓛 (complementValues 𝓛 U) := by
  rw [wilsonSpecificationAt_complementValues]
  simp only [glueOnLinks_eq_splice]
  rw [← WilsonOperator.kernelOperator_eq_integral ha h𝓛 β F U]
  exact specKernel_eq_kernelOperator ha β (linkWindowOfFinset 𝓛 h𝓛) h𝓛 F U
theorem complementSigma_eq_exteriorSigma (W : LinkWindow a) :
    complementSigma W.links = W.exteriorSigma := by
  have hset : complementLinks W.links = {b | b.IsPositivelyOriented ∧ b ∉ W.links} := by
    ext b
    simp only [complementLinks, mem_sdiff, mem_positiveLinks_iff, Finset.mem_coe, mem_ofPred_eq]
  unfold complementSigma LinkWindow.exteriorSigma
  rw [hset]
theorem kernelBasicProps_of_window {β : ℝ} (ha : 0 < a) (hs : SpecificationProperties ha β)
    (W : LinkWindow a) (h𝓛 : (W.links : Set (Link a)) ⊆ positiveLinkSet a) :
    KernelBasicProps ha β W.links h𝓛 := by
  have hk := specKernel_eq_conditionalExpectation ha β W h𝓛
  have hσ := complementSigma_eq_exteriorSigma W
  have hspec := fun U => isProbabilityMeasure_wilsonSpecification β W.links U
  have hprob : ∀ U, IsProbabilityMeasure
      (wilsonSpecificationAt ha β W.links (complementValues W.links U)) := fun U => by
    rw [wilsonSpecificationAt_complementValues]
    exact hspec U
  have hint : ∀ (F : GaugeField a → ℂ) (U : GaugeField a), IsBoundedObservable F →
      specKernel ha β W.links h𝓛 F U =
        ∫ U', F U' ∂specImage ha β W.links h𝓛 U := fun F U hF => by
    rw [specKernel_eq_integral, specImage,
      integral_map (measurable_glueOnLinks ha W.links h𝓛 U).aemeasurable
        hF.1.aestronglyMeasurable]
  refine ⟨fun F hF => ?_, fun U => ⟨?_, fun F hF => ⟨hint F U hF, ?_⟩⟩,
    fun F H hF hH hHm => ?_, fun F hF => ?_⟩
  · obtain ⟨h₁, h₂, h₃⟩ := (hs W).2.2.2.2.2.2.1 F hF
    rw [hk F, hσ]
    exact ⟨h₁, h₂, h₃⟩
  · have := hprob U
    exact Measure.isProbabilityMeasure_map
      (measurable_glueOnLinks ha W.links h𝓛 U).aemeasurable
  · exact specKernel_eq_integral ha β W.links h𝓛 F U
  · rw [hσ] at hHm
    have h := (hs W).2.2.2.2.2.2.2.1 F H hF hH hHm
    have e : (fun U => H U * F U) = F * H := by
      funext U
      simp [mul_comm]
    rw [e, hk, hk, h]
    rfl
  · rw [hk]
    exact (hs W).2.2.2.2.2.2.2.2.2.1 F hF
def InvariantOnObservables (ha : 0 < a) (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  ∀ W : LinkWindow a, ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν
theorem kernelCondExp_of_invariant {β : ℝ} (ha : 0 < a) (hs : SpecificationProperties ha β)
    {ν : Measure (GaugeField a)} (h : InvariantOnObservables ha β ν) :
    KernelCondExp ha β ν := by
  intro 𝓛 h𝓛 F hF
  have hp := kernelBasicProps_of_window ha hs (linkWindowOfFinset 𝓛 h𝓛) h𝓛
  obtain ⟨hobs, hm, -⟩ := hp.1 F hF
  refine ⟨hobs, hm, fun H hH hHm => ?_⟩
  have hEq := h (linkWindowOfFinset 𝓛 h𝓛) _ (isBoundedObservable_mul hH hF)
  rw [← specKernel_eq_conditionalExpectation ha β (linkWindowOfFinset 𝓛 h𝓛) h𝓛] at hEq
  have hmod : specKernel ha β 𝓛 h𝓛 (fun U => H U * F U) =
      fun U => H U * specKernel ha β 𝓛 h𝓛 F U := hp.2.2.1 F H hF hH hHm
  change ∫ U, specKernel ha β 𝓛 h𝓛 (fun U => H U * F U) U ∂ν = _ at hEq
  rw [hmod] at hEq
  simpa only [mul_comm] using hEq
theorem measurableSet_coord_preimage {S : Type} (j : S)
    {O : Set Matrices.ComplexMatrix2.specialUnitary} (hO : MeasurableSet O) :
    MeasurableSet[borel (LinkVariables S)] ((fun v : LinkVariables S => v j) ⁻¹' O) := by
  let _ : MeasurableSpace (LinkVariables S) := borel (LinkVariables S)
  have : BorelSpace (LinkVariables S) := ⟨rfl⟩
  exact (continuous_apply j).measurable hO
theorem measurableSet_restrictField_preimage (S : Set (Link a)) {B : Set (LinkVariables S)}
    (hB : MeasurableSet[borel (LinkVariables S)] B) :
    MeasurableSet {U : GaugeField a | restrictField U S ∈ B} := by
  let _ : MeasurableSpace (LinkVariables S) := borel (LinkVariables S)
  have : BorelSpace (LinkVariables S) := ⟨rfl⟩
  exact (continuous_restrictField S).measurable hB
def cylinderRect (𝓛 : Finset (Link a)) (B₁ : Set (LinkVariables (𝓛 : Set (Link a))))
    (B₂ : Set (ComplementVariables 𝓛)) : Set (GaugeField a) :=
  {U | restrictField U (𝓛 : Set (Link a)) ∈ B₁ ∧ complementValues 𝓛 U ∈ B₂}
theorem measurableSet_cylinderRect (𝓛 : Finset (Link a))
    {B₁ : Set (LinkVariables (𝓛 : Set (Link a)))} {B₂ : Set (ComplementVariables 𝓛)}
    (hB₁ : MeasurableSet[borel (LinkVariables (𝓛 : Set (Link a)))] B₁)
    (hB₂ : MeasurableSet[borel (ComplementVariables 𝓛)] B₂) :
    MeasurableSet (cylinderRect 𝓛 B₁ B₂) :=
  (measurableSet_restrictField_preimage _ hB₁).inter
    (measurableSet_restrictField_preimage _ hB₂)
theorem indicator_cylinderRect (𝓛 : Finset (Link a))
    (B₁ : Set (LinkVariables (𝓛 : Set (Link a)))) (B₂ : Set (ComplementVariables 𝓛)) :
    (cylinderRect 𝓛 B₁ B₂).indicator (1 : GaugeField a → ℂ) =
      observableOfLinks 𝓛 (setIndicator B₁) * observableOfComplement 𝓛 (setIndicator B₂) := by
  funext U
  by_cases h₁ : restrictField U (𝓛 : Set (Link a)) ∈ B₁ <;>
    by_cases h₂ : complementValues 𝓛 U ∈ B₂ <;>
    simp [cylinderRect, observableOfLinks, observableOfComplement, setIndicator, indicator, h₁, h₂]
theorem real_cylinderRect (ν : Measure (GaugeField a)) [IsFiniteMeasure ν] (𝓛 : Finset (Link a))
    {B₁ : Set (LinkVariables (𝓛 : Set (Link a)))} {B₂ : Set (ComplementVariables 𝓛)}
    (hB₁ : MeasurableSet[borel (LinkVariables (𝓛 : Set (Link a)))] B₁)
    (hB₂ : MeasurableSet[borel (ComplementVariables 𝓛)] B₂) :
    ((ν.real (cylinderRect 𝓛 B₁ B₂) : ℝ) : ℂ) =
      ∫ U, observableOfLinks 𝓛 (setIndicator B₁) U *
        observableOfComplement 𝓛 (setIndicator B₂) U ∂ν := by
  have h : ∫ U, (cylinderRect 𝓛 B₁ B₂).indicator (1 : GaugeField a → ℂ) U ∂ν =
      ∫ _ in cylinderRect 𝓛 B₁ B₂, (1 : ℂ) ∂ν :=
    integral_indicator (measurableSet_cylinderRect 𝓛 hB₁ hB₂)
  rw [indicator_cylinderRect] at h
  change ∫ U, observableOfLinks 𝓛 (setIndicator B₁) U *
    observableOfComplement 𝓛 (setIndicator B₂) U ∂ν = _ at h
  rw [h]
  simp [Measure.real]
theorem dlrRectangles_of_kernelCondExpInner {β : ℝ} (ha : 0 < a)
    (hD : ConfigurationSpace.MeasurableOnLinksCharacterization a)
    {ν : Measure (GaugeField a)} [IsFiniteMeasure ν]
    (h : KernelCondExpInner ha β ν) : DLRRectangles ha β ν := by
  intro 𝓛 h𝓛 B₁ B₂ hB₁ hB₂
  have hφ := setIndicator_mem_boundedBorelSpace hB₁
  have hχ := setIndicator_mem_boundedBorelSpace hB₂
  have hHobs := isBoundedObservable_observableOfComplement 𝓛 hχ
  have hHm : Measurable[complementSigma 𝓛] (observableOfComplement 𝓛 (setIndicator B₂)) :=
    (hD.2 𝓛 h𝓛 _ hHobs).2 ⟨_, hχ, fun _ => rfl⟩
  have hv := (h 𝓛 h𝓛 _ hφ).2.2 _ hHobs hHm
  have hr := real_cylinderRect ν 𝓛 hB₁ hB₂
  change ((ν.real {U | restrictField U (𝓛 : Set (Link a)) ∈ B₁ ∧ complementValues 𝓛 U ∈ B₂} : ℝ) : ℂ) =
    _ at hr
  rw [hr, ← hv]
  simp only [mul_comm]
theorem invariant_of_dlrRectangles {β : ℝ} (ha : 0 < a) (hs : SpecificationProperties ha β)
    (hD : ConfigurationSpace.MeasurableOnLinksCharacterization a)
    {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    (h : DLRRectangles ha β ν) : InvariantOnObservables ha β ν := by
  intro W F hF
  obtain ⟨ν', hprob', hmass, hint⟩ := (hs W).2.2.2.2.2.2.2.2.2.2 ν inferInstance
  have h𝓛 := links_subset_positiveLinks W
  let C : Set (Set (GaugeField a)) := {E | ∃ (B₁ : Set (LinkVariables (W.links : Set (Link a))))
    (B₂ : Set (ComplementVariables W.links)),
      MeasurableSet[borel (LinkVariables (W.links : Set (Link a)))] B₁ ∧
      MeasurableSet[borel (ComplementVariables W.links)] B₂ ∧ E = cylinderRect W.links B₁ B₂}
  have hC : ∀ E ∈ C, MeasurableSet E := by
    rintro _ ⟨B₁, B₂, hB₁, hB₂, rfl⟩
    exact measurableSet_cylinderRect _ hB₁ hB₂
  have hpi : IsPiSystem C := by
    rintro _ ⟨B₁, B₂, hB₁, hB₂, rfl⟩ _ ⟨B₁', B₂', hB₁', hB₂', rfl⟩ -
    refine ⟨B₁ ∩ B₁', B₂ ∩ B₂', MeasurableSet.inter hB₁ hB₁', MeasurableSet.inter hB₂ hB₂', ?_⟩
    ext U
    simp only [cylinderRect, mem_inter_iff, mem_ofPred_eq]
    tauto
  have hpos : ∀ b ∈ positiveLinkSet a,
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance ≤
        MeasurableSpace.generateFrom C := by
    rintro b hb _ ⟨O, hO, rfl⟩
    apply MeasurableSpace.measurableSet_generateFrom
    by_cases hbL : b ∈ W.links
    · refine ⟨(fun v : LinkVariables (W.links : Set (Link a)) => v ⟨b, hbL⟩) ⁻¹' O, univ,
        measurableSet_coord_preimage _ hO, @MeasurableSet.univ _ (borel _), ?_⟩
      ext U
      simp [cylinderRect, restrictField]
    · refine ⟨univ, (fun v : ComplementVariables W.links => v ⟨b, hb, hbL⟩) ⁻¹' O,
        @MeasurableSet.univ _ (borel _), measurableSet_coord_preimage _ hO, ?_⟩
      ext U
      simp [cylinderRect, restrictField, complementValues]
  have hgen : (inferInstance : MeasurableSpace (GaugeField a)) =
      MeasurableSpace.generateFrom C :=
    le_antisymm ((WilsonOperator.borel_eq_linkSigmaAlgebra ha).le.trans (iSup₂_le hpos))
      (MeasurableSpace.generateFrom_le hC)
  have hagree : ∀ E ∈ C, ν' E = ν E := by
    rintro _ ⟨B₁, B₂, hB₁, hB₂, rfl⟩
    have hφ := setIndicator_mem_boundedBorelSpace hB₁
    have hχ := setIndicator_mem_boundedBorelSpace hB₂
    have hobs₁ := isBoundedObservable_observableOfLinks W.links hφ
    have hobs₂ := isBoundedObservable_observableOfComplement W.links hχ
    have hE := measurableSet_cylinderRect W.links hB₁ hB₂
    have h₁ := hmass _ hE
    have hHm : Measurable[W.exteriorSigma]
        (observableOfComplement W.links (setIndicator B₂)) := by
      rw [← complementSigma_eq_exteriorSigma]
      exact (hD.2 W.links h𝓛 _ hobs₂).2 ⟨_, hχ, fun _ => rfl⟩
    rw [indicator_cylinderRect, stateEval, (hs W).2.2.2.2.2.2.2.1 _ _ hobs₁ hobs₂ hHm] at h₁
    have h₂ := h W.links h𝓛 B₁ B₂ hB₁ hB₂
    rw [specKernel_eq_conditionalExpectation ha β W h𝓛] at h₂
    have h₃ : ((ν' (cylinderRect W.links B₁ B₂)).toReal : ℂ) =
        ((ν.real (cylinderRect W.links B₁ B₂) : ℝ) : ℂ) := h₁.trans h₂.symm
    have h₄ : (ν' (cylinderRect W.links B₁ B₂)).toReal = (ν (cylinderRect W.links B₁ B₂)).toReal := by
      exact_mod_cast h₃
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h₄
  have heq : ν' = ν := ext_of_generate_finite C hgen hpi hagree (by simp)
  have hfin := hint F hF
  rw [heq] at hfin
  exact hfin.symm
theorem tfae_of_probability {β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hs : SpecificationProperties ha β)
    (hD : ConfigurationSpace.MeasurableOnLinksCharacterization a)
    (hForms : GibbsClassEqGibbsStates)
    (ν : Measure (GaugeField a)) (hν : IsProbabilityMeasure ν) :
    List.TFAE [DLRRectangles ha β ν, KernelCondExpInner ha β ν,
        KernelCondExp ha β ν, KernelInvariant ha β ν] ∧
      (IsGibbs β ν ↔
        DLRRectangles ha β ν ∧ KernelCondExpInner ha β ν ∧
          KernelCondExp ha β ν ∧ KernelInvariant ha β ν) := by
  have hf := hForms.1 a ha β hβ ν hν
  have hEG : InvariantOnObservables ha β ν ↔ IsGibbs β ν := hf.out 1 2
  have h₃₂ : KernelCondExp ha β ν → KernelCondExpInner ha β ν :=
    fun h 𝓛 h𝓛 φ hφ => h 𝓛 h𝓛 _ (isBoundedObservable_observableOfLinks 𝓛 hφ)
  have h₂₁ : KernelCondExpInner ha β ν → DLRRectangles ha β ν :=
    dlrRectangles_of_kernelCondExpInner ha hD
  have h₁E : DLRRectangles ha β ν → InvariantOnObservables ha β ν :=
    invariant_of_dlrRectangles ha hs hD
  have hE₃ : InvariantOnObservables ha β ν → KernelCondExp ha β ν :=
    kernelCondExp_of_invariant ha hs
  have h₃₄ : KernelCondExp ha β ν → KernelInvariant ha β ν := by
    intro h 𝓛 h𝓛 F hF
    obtain ⟨hFo, -, -⟩ := id hF
    have hv := (h 𝓛 h𝓛 F hFo).2.2 (fun _ => 1)
      ⟨measurable_const, 1, fun _ => by simp⟩ (@measurable_const _ _ _ _ _)
    simpa using hv
  have h₄E : KernelInvariant ha β ν → InvariantOnObservables ha β ν := by
    intro h
    have h₀₁ : ν ∈ gibbsClass ha β → InvariantOnObservables ha β ν := (hf.out 0 1).1
    refine h₀₁ ⟨hν, fun W F hF => ?_⟩
    have := h W.links (links_subset_positiveLinks W) F hF
    rwa [specKernel_eq_conditionalExpectation ha β W (links_subset_positiveLinks W)] at this
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 3 := fun h => hE₃ (h₁E h)
    tfae_have 3 → 2 := h₃₂
    tfae_have 2 → 1 := h₂₁
    tfae_have 3 → 4 := h₃₄
    tfae_have 4 → 3 := fun h => hE₃ (h₄E h)
    tfae_finish
  · constructor
    · intro h
      have h₃ := hE₃ (hEG.2 h)
      exact ⟨h₂₁ (h₃₂ h₃), h₃₂ h₃, h₃, h₃₄ h₃⟩
    · rintro ⟨h, -⟩
      exact hEG.1 (h₁E h)
theorem kernelOrientationInvariant_holds {β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hC : ConfigurationSpace.FaceEnergyAndBoltzmannWeight a)
    (hProducts : CountableProductTheorem) :
    KernelOrientationInvariant ha β := by
  classical
  intro 𝓛' h
  let pos : Link a → Link a := fun c => if c ∈ positiveLinkSet a then c else c.opposite
  have hpos_of : ∀ {c : Link a}, c ∈ positiveLinkSet a → pos c = c := fun hc => if_pos hc
  have hneg_of : ∀ {c : Link a}, c ∉ positiveLinkSet a → pos c = c.opposite :=
    fun hc => if_neg hc
  have hpos_mem : ∀ c, pos c ∈ positiveLinkSet a := fun c => by
    by_cases hc : c ∈ positiveLinkSet a
    · rwa [hpos_of hc]
    · rw [hneg_of hc]
      exact (mem_positiveLinks_or_opposite_mem c).resolve_left hc
  let 𝓛 : Finset (Link a) := 𝓛'.image pos
  have h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hpos_mem c
  have hmem : ∀ {b : Link a}, b ∈ 𝓛 ↔
      b ∈ positiveLinkSet a ∧ (b ∈ 𝓛' ∨ b.opposite ∈ 𝓛') := by
    intro b
    constructor
    · intro hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
      refine ⟨hpos_mem c, ?_⟩
      by_cases hcp : c ∈ positiveLinkSet a
      · rw [hpos_of hcp]
        exact Or.inl hc
      · rw [hneg_of hcp, Link.opposite_opposite]
        exact Or.inr hc
    · rintro ⟨hb, h₁ | h₁⟩
      · exact Finset.mem_image.2 ⟨b, h₁, hpos_of hb⟩
      · refine Finset.mem_image.2 ⟨b.opposite, h₁, ?_⟩
        rw [hneg_of (opposite_notMem_positiveLinks ha hb), Link.opposite_opposite]
  have hset : (𝓛 : Set (Link a)) = positivePart 𝓛' := by
    ext b
    simp only [Finset.mem_coe, hmem, positivePart, mem_ofPred_eq]
    refine and_congr_right fun _ => or_congr_right ?_
    constructor
    · intro hr
      exact ⟨b.opposite, hr, (Link.opposite_opposite b).symm⟩
    · rintro ⟨c, hc, rfl⟩
      rwa [Link.opposite_opposite]
  have hpl : plaquettesTouching 𝓛' = plaquettesTouching 𝓛 := by
    ext p
    rw [mem_plaquettesTouching_iff ha, mem_plaquettesTouching_iff ha]
    refine exists_congr fun b => and_congr_right fun hb => ?_
    have hbp := WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb
    have hr : b.opposite ∉ 𝓛 := fun hr => opposite_notMem_positiveLinks ha hbp (h𝓛 hr)
    constructor
    · exact fun h₀ => Or.inl (hmem.2 ⟨hbp, h₀⟩)
    · rintro (h₀ | h₀)
      · exact (hmem.1 h₀).2
      · exact absurd h₀ hr
  refine ⟨𝓛, h𝓛, hset, hpl, fun F hF => ?_⟩
  funext U
  have h₂ := hasNoOppositePairs_of_subset_positiveLinks ha h𝓛
  have hρ : Function.Bijective (fun c : (𝓛' : Set (Link a)) =>
      (⟨pos c.1, Finset.mem_coe.2 (Finset.mem_image_of_mem pos c.2)⟩ : (𝓛 : Set (Link a)))) := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ e
      have e' : pos c = pos c' := congrArg Subtype.val e
      apply Subtype.ext
      change c = c'
      by_cases h₁ : c ∈ positiveLinkSet a <;> by_cases h₃ : c' ∈ positiveLinkSet a
      · rwa [hpos_of h₁, hpos_of h₃] at e'
      · rw [hpos_of h₁, hneg_of h₃] at e'
        exact absurd (e' ▸ Finset.mem_coe.2 hc) (h c' (Finset.mem_coe.2 hc'))
      · rw [hneg_of h₁, hpos_of h₃] at e'
        exact absurd (e' ▸ Finset.mem_coe.2 hc') (h c (Finset.mem_coe.2 hc))
      · rw [hneg_of h₁, hneg_of h₃] at e'
        rw [← Link.opposite_opposite c, e', Link.opposite_opposite]
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      exact ⟨⟨c, Finset.mem_coe.2 hc⟩, rfl⟩
  let ρ : (𝓛' : Set (Link a)) ≃ (𝓛 : Set (Link a)) := Equiv.ofBijective _ hρ
  let M : Set (𝓛' : Set (Link a)) := {c | c.1 ∉ positiveLinkSet a}
  have hconf : ∀ V : LinkVariables (𝓛' : Set (Link a)),
      overwriteLinks h V U = overwriteLinks h₂ (reindexInvert ρ M V) U := by
    intro V
    set X := overwriteLinks h₂ (reindexInvert ρ M V) U with hX
    have hval : ∀ c : (𝓛' : Set (Link a)), X c.1 = V c := by
      intro c
      have hsymm : ρ.symm (ρ c) = c := ρ.symm_apply_apply c
      by_cases hc : c.1 ∈ positiveLinkSet a
      · have e : (ρ c).1 = c.1 := hpos_of hc
        have := overwriteLinks_apply_of_mem h₂ (reindexInvert ρ M V) U (ρ c)
        rw [e] at this
        rw [hX, this]
        simp only [reindexInvert, hsymm, M, mem_ofPred_eq, hc, not_true_eq_false, if_false]
      · have e : (ρ c).1.opposite = c.1 := by
          have : (ρ c).1 = c.1.opposite := hneg_of hc
          rw [this, Link.opposite_opposite]
        have := overwriteLinks_apply_opposite h₂ (reindexInvert ρ M V) U (ρ c)
        rw [e] at this
        rw [hX, this]
        simp only [reindexInvert, hsymm, M, mem_ofPred_eq, hc, not_false_eq_true, if_true,
          inv_inv]
    apply Subtype.ext
    funext b
    change overwriteLinks h V U b = X b
    by_cases hb : b ∈ (𝓛' : Set (Link a))
    · rw [overwriteLinks_apply_of_mem h V U ⟨b, hb⟩]
      exact (hval ⟨b, hb⟩).symm
    · by_cases hr : b.opposite ∈ (𝓛' : Set (Link a))
      · have h₁ := overwriteLinks_apply_opposite h V U ⟨b.opposite, hr⟩
        have h₃ := WilsonOperator.gaugeField_apply_opposite X b
        simp only [Link.opposite_opposite] at h₁
        rw [h₁, h₃, hval ⟨b.opposite, hr⟩]
      · have hb₁ : b ∉ (𝓛 : Set (Link a)) := fun h₁ =>
          ((hmem.1 (Finset.mem_coe.1 h₁)).2.elim hb hr)
        have hb₂ : b.opposite ∉ (𝓛 : Set (Link a)) := fun h₁ => by
          have := (hmem.1 (Finset.mem_coe.1 h₁)).2
          rw [Link.opposite_opposite] at this
          exact this.elim hr hb
        rw [overwriteLinks_apply_of_not_mem h V U hb hr, hX,
          overwriteLinks_apply_of_not_mem h₂ _ U hb₁ hb₂]
  have htransfer : ∀ G : GaugeField a → ℂ, IsBoundedObservable G →
      ∫ V, G (overwriteLinks h V U) ∂LinkVariables.haarMeasure (𝓛' : Set (Link a)) =
        ∫ V, G (overwriteLinks h₂ V U) ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) := by
    intro G hG
    have hcont : Continuous fun V : LinkVariables (𝓛 : Set (Link a)) => overwriteLinks h₂ V U :=
      OrientedLinkSet.continuous_glue ⟨𝓛, h₂⟩ U
    have hΦ : (fun V => G (overwriteLinks h₂ V U)) ∈
        boundedBorelSpace (LinkVariables (𝓛 : Set (Link a))) := by
      obtain ⟨hm, C, hC⟩ := hG
      let _ : MeasurableSpace (LinkVariables (𝓛 : Set (Link a))) :=
        borel (LinkVariables (𝓛 : Set (Link a)))
      have : BorelSpace (LinkVariables (𝓛 : Set (Link a))) := ⟨rfl⟩
      exact ⟨hm.comp hcont.measurable, C, fun V => hC _⟩
    have := ((hProducts.2 (𝓛' : Set (Link a))).2 (𝓛 : Set (Link a)) ρ M).2 ⟨_, hΦ⟩
    simp only [hconf]
    exact this
  have hW : wilsonLinkEnergy β 𝓛' = wilsonLinkEnergy β 𝓛 := by
    funext U'
    simp only [wilsonLinkEnergy, hpl]
  obtain ⟨-, hg, -⟩ := (hC.2 𝓛 h₂ β hβ).2.1
  have hnum := htransfer _ (isBoundedObservable_mul hF hg)
  have hden := htransfer _ hg
  simp only [specKernel, wilsonLinkKernel, linkKernel, hW]
  have hd : ((∫ V, Real.exp (-wilsonLinkEnergy β 𝓛 (overwriteLinks h V U))
        ∂LinkVariables.haarMeasure (𝓛' : Set (Link a)) : ℝ) : ℂ) =
      ((∫ V, Real.exp (-wilsonLinkEnergy β 𝓛
          (overwriteLinks (hasNoOppositePairs_of_subset_positiveLinks ha h𝓛) V U))
        ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact hden
  exact congrArg₂ (· / ·) hnum hd
theorem integral_convexCombination {ν₁ ν₂ : Measure (GaugeField a)} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) {A : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) :
    ∫ U, A U ∂(ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂) =
      t • ∫ U, A U ∂ν₁ + (1 - t) • ∫ U, A U ∂ν₂ := by
  rw [integral_add_measure
      ((integrable_of_isBoundedObservable ν₁ hA).smul_measure ENNReal.ofReal_ne_top)
      ((integrable_of_isBoundedObservable ν₂ hA).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal h₀,
    ENNReal.toReal_ofReal (sub_nonneg.2 h₁)]
theorem isPeriodicGibbs_convexCombination {β : ℝ} (ha : 0 < a)
    (hgibbs : ∀ ν : Measure (GaugeField a),
      IsProbabilityMeasure ν → (IsGibbs β ν ↔ KernelInvariant ha β ν))
    (hobs : ∀ (𝓛 : Finset (Link a)) (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a)
      (F : GaugeField a → ℂ), IsBoundedObservable F →
        IsBoundedObservable (specKernel ha β 𝓛 h𝓛 F))
    (ν₁ ν₂ : Measure (GaugeField a)) (h₁ : IsPeriodicGibbs β ν₁)
    (h₂ : IsPeriodicGibbs β ν₂) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsPeriodicGibbs β (ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂) := by
  obtain ⟨g₁, H₁, f₁, i₁⟩ := h₁
  obtain ⟨g₂, H₂, f₂, i₂⟩ := h₂
  have p₁ := g₁.1
  have p₂ := g₂.1
  have hprob : IsProbabilityMeasure (ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂) := by
    refine ⟨?_⟩
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht₀ (sub_nonneg.2 ht₁)]
    simp
  refine ⟨(hgibbs _ hprob).2 fun 𝓛 h𝓛 F hF => ?_, H₁ ⊓ H₂, ?_, fun v hv A hA => ?_⟩
  · obtain ⟨hFo, -, -⟩ := id hF
    rw [integral_convexCombination ht₀ ht₁ (hobs 𝓛 h𝓛 F hFo), integral_convexCombination ht₀ ht₁ hFo,
      (hgibbs ν₁ p₁).1 g₁ 𝓛 h𝓛 F hF, (hgibbs ν₂ p₂).1 g₂ 𝓛 h𝓛 F hF]
  · have := f₁
    have := f₂
    infer_instance
  · have hT := hA.actOn (shift v)
    rw [integral_convexCombination ht₀ ht₁ hT, integral_convexCombination ht₀ ht₁ hA,
      i₁ v hv.1 A hA, i₂ v hv.2 A hA]
theorem gibbsEquivalenceStatement_proof (hFacts : SpecificationPropertiesAtEveryMesh)
    (hForms : GibbsClassEqGibbsStates)
    (hSpace : ConfigurationSpace.Main)
    (hProducts : CountableProductTheorem) : GibbsEquivalenceStatement := by
  intro a β ha hβ
  have hs := hFacts a β ha hβ
  obtain ⟨-, -, hC, hD, -, -, -⟩ := hSpace a ha
  have hforms := fun ν hν => tfae_of_probability ha hβ hs hD hForms ν hν
  refine ⟨kernelOrientationInvariant_holds ha hβ hC hProducts,
    fun 𝓛 h𝓛 => kernelBasicProps_of_window ha hs (linkWindowOfFinset 𝓛 h𝓛) h𝓛, hforms, ?_⟩
  refine isPeriodicGibbs_convexCombination ha (fun ν hν => ?_) (fun 𝓛 h𝓛 F hF => ?_)
  · obtain ⟨ht, hg⟩ := hforms ν hν
    exact ⟨fun h => (hg.1 h).2.2.2, fun h => hg.2 ⟨(ht.out 3 0).1 h, (ht.out 3 1).1 h,
      (ht.out 3 2).1 h, h⟩⟩
  · exact ((kernelBasicProps_of_window ha hs (linkWindowOfFinset 𝓛 h𝓛) h𝓛).1 F hF).1
end YangMills.Construction.InfiniteLattice.GibbsEquivalences
