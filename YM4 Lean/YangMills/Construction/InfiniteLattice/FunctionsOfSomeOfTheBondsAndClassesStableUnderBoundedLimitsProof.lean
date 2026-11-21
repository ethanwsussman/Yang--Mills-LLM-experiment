import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate NNReal
noncomputable section
namespace YangMills.Construction
open InfiniteLattice InfiniteLattice.WilsonOperator
namespace FieldsAtSpacing.LinkFunctions
variable {a : ℝ}
attribute [local instance] secondCountable_specialUnitary countable_link
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b :=
  (continuous_apply b).comp
    (continuous_subtype_val
      (p := fun U : Link a → Matrices.ComplexMatrix2.specialUnitary => ∀ b, U b.opposite = (U b)⁻¹))
theorem continuous_linkRestriction (L : Set (Link a)) : Continuous (linkRestriction L) :=
  continuous_pi fun b => continuous_eval_link (b : Link a)
theorem ext_of_eq_on_positiveLinks {U V : GaugeField a}
    (h : ∀ b ∈ positiveLinkSet a, U b = V b) : U = V := by
  refine Subtype.ext (funext fun b => ?_)
  rcases mem_positiveLinks_or_opposite_mem b with hb | hb
  · exact h b hb
  · change U b = V b
    rw [gaugeField_apply_opposite U b, gaugeField_apply_opposite V b, h _ hb]
theorem compactSpace_gaugeField (ha : 0 < a) : CompactSpace (GaugeField a) :=
  (gaugeFieldHomeomorph ha).symm.compactSpace
theorem t2Space_gaugeField (ha : 0 < a) : T2Space (GaugeField a) :=
  (gaugeFieldHomeomorph ha).symm.t2Space
theorem continuous_glueOnLinks (ha : 0 < a) {L : Set (Link a)} (hL : L ⊆ positiveLinkSet a) :
    Continuous (fun q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L) =>
      glueOnLinks ha hL q.1 q.2) := by
  have pos : ∀ b ∈ positiveLinkSet a,
      Continuous fun q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L) =>
        glueOnLinks ha hL q.1 q.2 b := by
    intro b hb
    by_cases h : b ∈ L
    · have e : ∀ q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L),
          glueOnLinks ha hL q.1 q.2 b = q.1 ⟨b, h⟩ :=
        fun q => glueOnLinks_apply_of_mem ha hL q.1 q.2 ⟨b, h⟩
      simp only [e]
      exact (continuous_apply _).comp continuous_fst
    · have e : ∀ q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L),
          glueOnLinks ha hL q.1 q.2 b = q.2 ⟨b, hb, h⟩ :=
        fun q => glueOnLinks_apply_of_mem_diff ha hL q.1 q.2 ⟨b, hb, h⟩
      simp only [e]
      exact (continuous_apply _).comp continuous_snd
  have key : Continuous fun q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L) =>
      ((glueOnLinks ha hL q.1 q.2 : GaugeField a) :
        Link a → Matrices.ComplexMatrix2.specialUnitary) := by
    refine continuous_pi fun b => ?_
    rcases mem_positiveLinks_or_opposite_mem b with h | h
    · exact pos b h
    · have e : ∀ q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L),
          glueOnLinks ha hL q.1 q.2 b = (glueOnLinks ha hL q.1 q.2 b.opposite)⁻¹ :=
        fun q => gaugeField_apply_opposite _ b
      simp only [e]
      exact (pos _ h).inv
  exact Continuous.subtype_mk key _
def extendByOne (ha : 0 < a) {L : Set (Link a)} (hL : L ⊆ positiveLinkSet a)
    (g : LinkVariables L) : GaugeField a :=
  glueOnLinks ha hL g fun _ => 1
theorem continuous_extendByOne (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) : Continuous (extendByOne ha hL) :=
  (continuous_glueOnLinks ha hL).comp (continuous_id.prodMk continuous_const)
theorem linkRestriction_extendByOne (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) (g : LinkVariables L) :
    linkRestriction L (extendByOne ha hL g) = g :=
  funext fun b => glueOnLinks_apply_of_mem ha hL g _ b
theorem linkRestriction_surjective (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) : Function.Surjective (linkRestriction L) :=
  fun g => ⟨extendByOne ha hL g, linkRestriction_extendByOne ha hL g⟩
theorem glueOnLinks_bijective (ha : 0 < a) {L : Set (Link a)} (hL : L ⊆ positiveLinkSet a) :
    Function.Bijective (fun q : LinkVariables L × LinkVariables ↥(positiveLinkSet a \ L) =>
      glueOnLinks ha hL q.1 q.2) := by
  constructor
  · rintro ⟨g, h⟩ ⟨g', h'⟩ e
    have e' : glueOnLinks ha hL g h = glueOnLinks ha hL g' h' := e
    refine Prod.ext (funext fun b => ?_) (funext fun b => ?_)
    · have := congrArg (fun U : GaugeField a => U b) e'
      simpa only [glueOnLinks_apply_of_mem] using this
    · have := congrArg (fun U : GaugeField a => U b) e'
      simpa only [glueOnLinks_apply_of_mem_diff] using this
  · intro U
    refine ⟨(linkRestriction L U, linkRestriction _ U), ext_of_eq_on_positiveLinks fun b hb => ?_⟩
    by_cases h : b ∈ L
    · exact glueOnLinks_apply_of_mem ha hL _ _ ⟨b, h⟩
    · exact glueOnLinks_apply_of_mem_diff ha hL _ _ ⟨b, hb, h⟩
theorem borel_linkVariables_eq_iSup (ι : Type) [Countable ι] :
    borel (LinkVariables ι) =
      ⨆ b : ι, MeasurableSpace.comap (fun g : LinkVariables ι => g b)
        (borel Matrices.ComplexMatrix2.specialUnitary) := by
  have h : BorelSpace (LinkVariables ι) := Pi.borelSpace
  exact h.measurable_eq.symm
theorem linkSigma_eq_comap (L : Set (Link a)) :
    linkSigma L = MeasurableSpace.comap (linkRestriction L) (borel (LinkVariables L)) := by
  rw [borel_linkVariables_eq_iSup, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  exact iSup_subtype' (f := fun (b : Link a) (_ : b ∈ L) =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance)
theorem linkSpaceStructure (ha : 0 < a) {L : Set (Link a)} (hL : L ⊆ positiveLinkSet a) :
    LinkSpaceStructure ha hL := by
  have := compactSpace_gaugeField ha
  have := t2Space_gaugeField ha
  refine ⟨inferInstance, inferInstance, borel_linkVariables_eq_iSup _, ?_,
    continuous_linkRestriction L, linkRestriction_surjective ha hL, borel_eq_linkSigmaAlgebra ha, ?_⟩
  · exact isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_glueOnLinks ha hL, glueOnLinks_bijective ha hL⟩
  · ext A
    change MeasurableSet[linkSigma L] A ↔ ∃ E : Set (LinkVariables L),
      MeasurableSet[borel (LinkVariables L)] E ∧ A = linkRestriction L ⁻¹' E
    rw [linkSigma_eq_comap]
    constructor
    · rintro ⟨E, hE, rfl⟩
      exact ⟨E, hE, rfl⟩
    · rintro ⟨E, hE, rfl⟩
      exact ⟨E, hE, rfl⟩
theorem dependsOnlyOnLinks_of_isLinkMeasurable {L : Set (Link a)} {F : GaugeField a → ℂ}
    (h : IsLinkMeasurable L F) : DependsOnlyOnLinks L F := by
  intro U V hUV
  have hs : MeasurableSet[linkSigma L] (F ⁻¹' {F U}) := h (measurableSet_singleton _)
  rw [linkSigma_eq_comap] at hs
  obtain ⟨E, _, hE⟩ := hs
  have h1 : linkRestriction L U ∈ E := by
    have : U ∈ linkRestriction L ⁻¹' E := by
      rw [hE]
      rfl
    exact this
  have hR : linkRestriction L V = linkRestriction L U :=
    funext fun b => (hUV b b.2).symm
  have h2 : V ∈ F ⁻¹' {F U} := by
    rw [← hE]
    change linkRestriction L V ∈ E
    rw [hR]
    exact h1
  exact (show F V = F U from h2).symm
theorem factorsThroughLinks_of_dependsOnlyOnLinks (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : DependsOnlyOnLinks L F) : FactorsThroughLinks L F := by
  obtain ⟨hm, C, hC⟩ := hF
  refine ⟨F ∘ extendByOne ha hL, ?_, ⟨C, fun g => hC _⟩, ?_⟩
  · let _ : MeasurableSpace (LinkVariables L) := borel _
    have : BorelSpace (LinkVariables L) := ⟨rfl⟩
    exact hm.comp (continuous_extendByOne ha hL).measurable
  · funext U
    exact h U _ fun b hb => (congrFun (linkRestriction_extendByOne ha hL (linkRestriction L U))
      ⟨b, hb⟩).symm
theorem isLinkMeasurable_of_factorsThroughLinks {L : Set (Link a)} {F : GaugeField a → ℂ}
    (h : FactorsThroughLinks L F) : IsLinkMeasurable L F := by
  obtain ⟨f, ⟨hf, -, rfl⟩⟩ := h
  have hρ : @Measurable _ _ (linkSigma L) (borel _) (linkRestriction L) := by
    rw [linkSigma_eq_comap]
    exact comap_measurable _
  exact hf.comp hρ
theorem linkSupportCharacterizations (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) : LinkSupportCharacterizations L := by
  intro F hF
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := dependsOnlyOnLinks_of_isLinkMeasurable
    tfae_have 2 → 3 := factorsThroughLinks_of_dependsOnlyOnLinks ha hL hF
    tfae_have 3 → 1 := isLinkMeasurable_of_factorsThroughLinks
    tfae_finish
  · rintro f ⟨-, -, rfl⟩
    have hρ := linkRestriction_surjective ha hL
    refine ⟨?_, ?_, ?_⟩
    · rintro f' ⟨-, -, e⟩
      exact (hρ.injective_comp_right (congrArg id e.symm)).symm ▸ rfl
    · exact (hρ.iSup_comp fun g => ‖f g‖).symm
    · intro hc
      have e : f = (f ∘ linkRestriction L) ∘ extendByOne ha hL := by
        funext g
        simp only [Function.comp, linkRestriction_extendByOne]
      rw [e]
      exact hc.comp (continuous_extendByOne ha hL)
theorem hasLinkSupport_of_dependsOnlyOnLinks (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : DependsOnlyOnLinks L F) : HasLinkSupport L F :=
  have h3 := factorsThroughLinks_of_dependsOnlyOnLinks ha hL hF h
  ⟨isLinkMeasurable_of_factorsThroughLinks h3, h, h3⟩
theorem hasLinkSupport_of_isLinkMeasurable (ha : 0 < a) {L : Set (Link a)}
    (hL : L ⊆ positiveLinkSet a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : IsLinkMeasurable L F) : HasLinkSupport L F :=
  hasLinkSupport_of_dependsOnlyOnLinks ha hL hF (dependsOnlyOnLinks_of_isLinkMeasurable h)
theorem regionSigma_eq_linkSigma (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      linkSigma (positiveLinksWithin a S) := by
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    rcases mem_positiveLinks_or_opposite_mem b with h | h
    · exact le_iSup₂_of_le (f := fun (b : Link a) (_ : b ∈ positiveLinksWithin a S) =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b ⟨h, hb⟩ le_rfl
    · have hb' : b.opposite ∈ positiveLinksWithin a S := ⟨h, hb.2, hb.1⟩
      refine le_trans ?_ (le_iSup₂ (f := fun (b : Link a) (_ : b ∈ positiveLinksWithin a S) =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b.opposite hb')
      have e : (fun U : GaugeField a => U b) =
          (fun g : Matrices.ComplexMatrix2.specialUnitary => g⁻¹) ∘
            fun U : GaugeField a => U b.opposite :=
        funext fun U => gaugeField_apply_opposite U b
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (Measurable.comap_le continuous_inv.measurable)
  · exact biSup_mono fun b hb => hb.2
theorem linkSigma_le_borel (L : Set (Link a)) :
    linkSigma L ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  iSup₂_le fun b _ => Measurable.comap_le (continuous_eval_link b).measurable
theorem mem_regionObservables_iff {S : Set AmbientSpace} {F : GaugeField a → ℂ} :
    F ∈ boundedRegionObservables a S ↔ Measurable[regionSigma S] F ∧ ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C :=
  ⟨fun h => ⟨h.2, h.1.2⟩,
    fun h => ⟨⟨h.1.mono (linkSigma_le_borel _) le_rfl, h.2⟩, h.1⟩⟩
theorem exists_bound_exp_comp {X : Type*} {F : X → ℂ} (h : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    ∃ C : ℝ, ∀ x, ‖(Complex.exp ∘ F) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨Real.exp C, fun x => ?_⟩
  rw [Function.comp, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hC x))
def regionObservablesSubmodule (a : ℝ) (S : Set AmbientSpace) :
    Submodule ℂ (GaugeField a → ℂ) where
  carrier := boundedRegionObservables a S
  add_mem' := by
    intro F G hF hG
    obtain ⟨hF, C, hC⟩ := mem_regionObservables_iff.mp hF
    obtain ⟨hG, D, hD⟩ := mem_regionObservables_iff.mp hG
    exact mem_regionObservables_iff.mpr ⟨hF.add hG, C + D, fun U =>
      (norm_add_le _ _).trans (add_le_add (hC U) (hD U))⟩
  zero_mem' := mem_regionObservables_iff.mpr ⟨measurable_const, 0, fun _ => by simp⟩
  smul_mem' := by
    intro z F hF
    obtain ⟨hF, C, hC⟩ := mem_regionObservables_iff.mp hF
    refine mem_regionObservables_iff.mpr ⟨hF.const_smul z, ‖z‖ * C, fun U => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg z)
theorem regionObservablesProperties (ha : 0 < a) (L : Set (Link a)) :
    RegionObservablesProperties a L := by
  refine ⟨fun S => ⟨regionSigma_eq_linkSigma S, ?_, ⟨regionObservablesSubmodule a S, rfl⟩,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · ext F
    constructor
    · rintro ⟨hO, hM⟩
      refine ⟨hO, hasLinkSupport_of_isLinkMeasurable ha inter_subset_left hO ?_⟩
      have e := regionSigma_eq_linkSigma (a := a) S
      change Measurable[linkSigma (positiveLinksWithin a S)] F
      rw [← e]
      exact hM
    · rintro ⟨hO, hM, -, -⟩
      refine ⟨hO, ?_⟩
      have e := regionSigma_eq_linkSigma (a := a) S
      change Measurable[regionSigma S] F
      rw [e]
      exact hM
  · intro F hF G hG
    obtain ⟨hF, C, hC⟩ := mem_regionObservables_iff.mp hF
    obtain ⟨hG, D, hD⟩ := mem_regionObservables_iff.mp hG
    refine mem_regionObservables_iff.mpr ⟨hF.mul hG, C * D, fun U => ?_⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  · intro F hF
    obtain ⟨hF, C, hC⟩ := mem_regionObservables_iff.mp hF
    refine mem_regionObservables_iff.mpr
      ⟨Complex.continuous_conj.measurable.comp hF, C, fun U => ?_⟩
    rw [RCLike.norm_conj]
    exact hC U
  · intro F hF
    obtain ⟨hF, hC⟩ := mem_regionObservables_iff.mp hF
    exact mem_regionObservables_iff.mpr ⟨Complex.measurable_exp.comp hF, exists_bound_exp_comp hC⟩
  · rintro S S' hS F ⟨hO, hM⟩
    refine ⟨hO, hM.mono ?_ le_rfl⟩
    exact biSup_mono fun b hb => ⟨hS hb.1, hS hb.2⟩
  · intro F hF
    constructor
    · exact hasLinkSupport_of_isLinkMeasurable ha diff_subset hF
    · exact fun h => h.1
theorem finite_latticePoints_of_isBounded (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge (R / a)
  have hfin : (Set.pi univ fun _ : Fin 4 => Set.Icc (-(N : ℤ)) N).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  let ψ : (Fin 4 → ℤ) → LatticePoint a := fun n => ⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩
  refine (hfin.image ψ).subset fun x hx => ?_
  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, fun μ _ => ?_, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  have h1 : ‖(x : AmbientSpace) μ‖ ≤ R := by
    have h0 := norm_le_pi_norm (x : AmbientSpace) μ
    have h2 : ‖(x : AmbientSpace)‖ ≤ R := mem_closedBall_zero_iff.mp (hR hx)
    exact h0.trans h2
  rw [hn μ, Real.norm_eq_abs, abs_mul, abs_of_pos ha] at h1
  have h3 : |(n μ : ℝ)| ≤ N := ((le_div_iff₀ ha).mpr h1).trans hN
  have h4 : |n μ| ≤ (N : ℤ) := by exact_mod_cast h3
  exact abs_le.mp h4
theorem finite_positiveLinksWithin (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : (positiveLinksWithin a S).Finite := by
  refine (((finite_latticePoints_of_isBounded ha hS).prod (finite_univ (α := Fin 4))).image
    fun q => Link.forwardFrom q.1 q.2).subset ?_
  rintro b ⟨⟨x, κ, rfl⟩, hb⟩
  exact ⟨(x, κ), ⟨hb.1, mem_univ _⟩, rfl⟩
def linkEndpoints (K : Set (Link a)) : Set AmbientSpace :=
  (fun b : Link a => (b.initial : AmbientSpace)) '' K ∪
    (fun b : Link a => (b.terminal : AmbientSpace)) '' K
theorem subset_positiveLinksWithin_linkEndpoints {K : Set (Link a)}
    (h : K ⊆ positiveLinkSet a) : K ⊆ positiveLinksWithin a (linkEndpoints K) :=
  fun b hb => ⟨h hb, Or.inl ⟨b, hb, rfl⟩, Or.inr ⟨b, hb, rfl⟩⟩
theorem isBounded_linkEndpoints {K : Set (Link a)} (h : K.Finite) :
    Bornology.IsBounded (linkEndpoints K) :=
  ((h.image _).union (h.image _)).isBounded
theorem exists_bound_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C := by
  have := compactSpace_gaugeField ha
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun U => hC U (mem_univ U)⟩
theorem isBoundedObservable_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F :=
  ⟨hF.measurable, exists_bound_of_continuous ha hF⟩
theorem mem_regionObservables_of_dependsOnlyOnLinks (ha : 0 < a) {S : Set AmbientSpace}
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : DependsOnlyOnLinks (positiveLinksWithin a S) F) :
    F ∈ boundedRegionObservables a S := by
  refine ⟨hF, ?_⟩
  have hM := (hasLinkSupport_of_dependsOnlyOnLinks ha inter_subset_left hF h).1
  change Measurable[regionSigma S] F
  rw [regionSigma_eq_linkSigma]
  exact hM
theorem mem_continuousFiniteLinkFunctions_of_dependsOnlyOnLinks (ha : 0 < a) {K : Set (Link a)}
    (hfin : K.Finite) (hK : K ⊆ positiveLinkSet a) {F : GaugeField a → ℂ} (hF : Continuous F)
    (h : DependsOnlyOnLinks K F) : F ∈ continuousFiniteLinkFunctions a := by
  obtain ⟨f, hf⟩ := factorsThroughLinks_of_dependsOnlyOnLinks ha hK
    (isBoundedObservable_of_continuous ha hF) h
  refine ⟨hF, K, hfin, hK, f, ((linkSupportCharacterizations ha hK) F
    (isBoundedObservable_of_continuous ha hF)).2 f hf |>.2.2 hF, fun U => congrFun hf.2.2 U⟩
theorem boundedRegionFiniteness (ha : 0 < a) : BoundedRegionFiniteness a := by
  refine ⟨fun S hS => finite_latticePoints_of_isBounded ha hS,
    fun S hS => finite_positiveLinksWithin ha hS,
    fun K hfin hK => ⟨linkEndpoints K, isBounded_linkEndpoints hfin,
      subset_positiveLinksWithin_linkEndpoints hK⟩, ?_⟩
  ext F
  constructor
  · rintro ⟨hF, K, hfin, hK, f, -, hf⟩
    have hF' : Continuous F := hF
    refine ⟨⟨linkEndpoints K, isBounded_linkEndpoints hfin,
      mem_regionObservables_of_dependsOnlyOnLinks ha
        (isBoundedObservable_of_continuous ha hF') fun U V hUV => ?_⟩, hF'⟩
    rw [hf U, hf V]
    exact congrArg f (funext fun b => hUV b (subset_positiveLinksWithin_linkEndpoints hK b.2))
  · rintro ⟨⟨S, hS, hO, hM⟩, hF⟩
    have hM' : IsLinkMeasurable (positiveLinksWithin a S) F := by
      change Measurable[linkSigma (positiveLinksWithin a S)] F
      rw [← regionSigma_eq_linkSigma]
      exact hM
    exact mem_continuousFiniteLinkFunctions_of_dependsOnlyOnLinks ha
      (finite_positiveLinksWithin ha hS) inter_subset_left hF
      (dependsOnlyOnLinks_of_isLinkMeasurable hM')
theorem norm_le_supNorm {F : GaugeField a → ℂ} (h : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := h
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem supNorm_le {F : GaugeField a → ℂ} {C : ℝ} (h : ∀ U, ‖F U‖ ≤ C) :
    observableSupNorm F ≤ C :=
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  ciSup_le h
theorem boundedLimitClassProperty (ha : 0 < a)
    (hmet : TopologicalSpace.MetrizableSpace (GaugeField a))
    (hdense : ∀ F ∈ continuousSubalgebra a, ∀ ε : ℝ, 0 < ε →
      ∃ G ∈ continuousFiniteLinkFunctions a, observableSupNorm (F - G) < ε) :
    BoundedLimitClassProperty a := by
  intro H hobs hloc hlim
  have hcont : ∀ F : GaugeField a → ℂ, Continuous F → F ∈ H := by
    intro F hF
    choose G hG hGF using fun n : ℕ => hdense F hF (1 / ((n : ℝ) + 1)) (by positivity)
    have hGc : ∀ n, Continuous (G n) := fun n => (hG n).1
    have hdiff : ∀ n U, ‖F U - G n U‖ ≤ 1 / ((n : ℝ) + 1) := fun n U =>
      (norm_le_supNorm (F := F - G n) (exists_bound_of_continuous ha (hF.sub (hGc n))) U).trans
        (hGF n).le
    obtain ⟨C, hC⟩ := exists_bound_of_continuous ha hF
    refine hlim G F (fun n => hloc (hG n)) ⟨C + 1, fun n => supNorm_le fun U => ?_⟩
      fun U => ?_
    · have h1 := hdiff n U
      have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc ‖G n U‖ = ‖F U - (F U - G n U)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖F U‖ + ‖F U - G n U‖ := norm_sub_le _ _
        _ ≤ C + 1 := by linarith [hC U]
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact hdiff n U
  have hclosed : ∀ E : Set (GaugeField a), IsClosed E →
      E.indicator (1 : GaugeField a → ℂ) ∈ H := by
    intro E hE
    refine hlim (fun n U => (((hE.apprSeq n U : ℝ≥0) : ℝ) : ℂ)) _ (fun n => hcont _ ?_)
      ⟨1, fun n => supNorm_le fun U => ?_⟩ fun U => ?_
    · exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hE.apprSeq n).continuous)
    · have h1 : hE.apprSeq n U ≤ 1 := HasOuterApproxClosed.apprSeq_apply_le_one hE n U
      have h2 : ((hE.apprSeq n U : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact h2
    · have h := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hE)) U
      have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h
      have e : E.indicator (1 : GaugeField a → ℂ) U =
          (Complex.ofReal ∘ NNReal.toReal) (E.indicator (fun _ => (1 : ℝ≥0)) U) := by
        by_cases hU : U ∈ E
        · rw [indicator_of_mem hU, indicator_of_mem hU]
          simp
        · rw [indicator_of_notMem hU, indicator_of_notMem hU]
          simp
      rw [e]
      exact h2
  have hone : (1 : GaugeField a → ℂ) ∈ H := hcont _ continuous_const
  have hind : ∀ E : Set (GaugeField a), MeasurableSet E →
      E.indicator (1 : GaugeField a → ℂ) ∈ H := by
    intro E hE
    refine MeasurableSpace.induction_on_inter
      (C := fun E _ => E.indicator (1 : GaugeField a → ℂ) ∈ H) (s := {E | IsClosed E})
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed)
      isPiSystem_isClosed ?_ (fun E hE => hclosed E hE) ?_ ?_ E hE
    · simp only [indicator_empty]
      exact H.zero_mem
    · intro E _ hE
      have e : Eᶜ.indicator (1 : GaugeField a → ℂ) = 1 - E.indicator 1 := by
        funext U
        by_cases hU : U ∈ E <;> simp [hU]
      rw [e]
      exact H.sub_mem hone hE
    · intro f hd _ hf
      have e : ∀ n : ℕ, ∑ i ∈ Finset.range n, (f i).indicator (1 : GaugeField a → ℂ) =
          (⋃ i ∈ Finset.range n, f i).indicator 1 := by
        intro n
        rw [Finset.indicator_biUnion _ _ (hd.set_pairwise _)]
        funext U
        simp
      refine hlim (fun n => ∑ i ∈ Finset.range n, (f i).indicator 1) _
        (fun n => H.sum_mem fun i _ => hf i)
        ⟨1, fun n => supNorm_le fun U => ?_⟩ fun U => ?_
      · simp only [e]
        by_cases hU : U ∈ ⋃ i ∈ Finset.range n, f i <;>
          simp only [indicator, hU, if_true, if_false] <;> simp
      · simp only [e]
        have hm : Monotone fun n : ℕ => ⋃ i ∈ Finset.range n, f i := fun m n hmn =>
          biUnion_subset_biUnion_left fun i hi => by
            simp only [Finset.coe_range, mem_Iio] at hi ⊢
            omega
        have ht := (Monotone.tendsto_indicator _ hm (1 : GaugeField a → ℂ) U).mono_right
          (pure_le_nhds _)
        have eu : (⋃ n : ℕ, ⋃ i ∈ Finset.range n, f i) = ⋃ i, f i := by
          ext x
          simp only [mem_iUnion, Finset.mem_range, exists_prop]
          exact ⟨fun ⟨_, i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i + 1, i, Nat.lt_succ_self i, h⟩⟩
        rwa [eu] at ht
  have hsimple : ∀ s : SimpleFunc (GaugeField a) ℂ, (s : GaugeField a → ℂ) ∈ H := by
    intro s
    refine SimpleFunc.induction (motive := fun s => (s : GaugeField a → ℂ) ∈ H) ?_ ?_ s
    · intro c E hE
      have e : ((SimpleFunc.piecewise E hE (SimpleFunc.const _ c) (SimpleFunc.const _ 0) :
          SimpleFunc (GaugeField a) ℂ) : GaugeField a → ℂ) = c • E.indicator 1 := by
        funext U
        by_cases hU : U ∈ E <;> simp [hU]
      rw [e]
      exact H.smul_mem c (hind E hE)
    · intro f g _ hf hg
      rw [SimpleFunc.coe_add]
      exact H.add_mem hf hg
  ext F
  constructor
  · exact hobs F
  · intro hF
    obtain ⟨hm, C, hC⟩ := hF
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (trivialField a))
    have hs := hm.stronglyMeasurable
    exact hlim (fun n => hs.approxBounded C n) F (fun n => hsimple _)
      ⟨C, fun n => supNorm_le fun U => StronglyMeasurable.norm_approxBounded_le hs hC0 n U⟩
      fun U => StronglyMeasurable.tendsto_approxBounded_of_norm_le hs (hC U)
theorem continuous_faceFunction (p : ElementaryPlaquette a) : Continuous (faceFunction p) := by
  have h : Continuous fun U : GaugeField a => faceHolonomy U p :=
    (((continuous_eval_link _).mul (continuous_eval_link _)).mul
      (continuous_eval_link _).inv).mul (continuous_eval_link _).inv
  have h2 : Continuous fun U : GaugeField a =>
      Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2) :=
    (continuous_subtype_val.comp h).matrix_trace
  exact Complex.continuous_ofReal.comp
    (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp h2)))
theorem faceEnergy_mem_Icc (U : Link a → Matrices.ComplexMatrix2.specialUnitary)
    (p : ElementaryPlaquette a) : faceEnergy U p ∈ Icc (0 : ℝ) 2 := by
  have hW := (faceHolonomy U p).2
  have h1 := entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hW) 0 0
  have h2 := entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup hW) 1 1
  have h3 : |(Matrices.ComplexMatrix2.fullTrace
      (faceHolonomy U p : Matrices.ComplexMatrix2)).re| ≤ 2 := by
    rw [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    linarith
  obtain ⟨h4, h5⟩ := abs_le.mp h3
  constructor <;> simp only [faceEnergy] <;> linarith
theorem faceFunction_dependsOnlyOnLinks (p : ElementaryPlaquette a) {K : Set (Link a)}
    (h : ∀ b ∈ edgeList p, b ∈ K) : DependsOnlyOnLinks K (faceFunction p) := by
  intro U V hUV
  simp only [faceFunction]
  rw [faceEnergy_congr p fun b hb => hUV b (h b hb)]
theorem mem_positiveLinksWithin_of_mem_edgeList {S : Set AmbientSpace}
    {p : ElementaryPlaquette a} (h : ContainsCorners S p) {b : Link a}
    (hb : b ∈ edgeList p) : b ∈ positiveLinksWithin a S := by
  refine ⟨mem_positiveLinks_of_mem_edgeList p hb, ?_⟩
  simp only [edgeList, List.mem_cons, List.not_mem_nil, or_false] at hb
  have c1 := h p.corner (by simp [ElementaryPlaquette.cornerSet])
  have c2 := h (p.corner + axisStep a p.lowAxis) (by simp [ElementaryPlaquette.cornerSet])
  have c3 := h (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
    (by simp [ElementaryPlaquette.cornerSet])
  have c4 := h (p.corner + axisStep a p.highAxis) (by simp [ElementaryPlaquette.cornerSet])
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨c1, c2⟩
  · exact ⟨c2, c3⟩
  · refine ⟨c4, ?_⟩
    change ((p.corner + axisStep a p.highAxis + axisStep a p.lowAxis : LatticePoint a) :
      AmbientSpace) ∈ S
    rwa [add_right_comm]
  · exact ⟨c1, c4⟩
theorem finite_plaquettes_center_mem (ha : 0 < a) {Q : Set AmbientSpace}
    (hQ : Bornology.IsBounded Q) : {p : ElementaryPlaquette a | p.center ∈ Q}.Finite := by
  obtain ⟨R, hR⟩ := hQ.subset_closedBall 0
  have hB : Bornology.IsBounded (Metric.closedBall (0 : AmbientSpace) (R + a)) :=
    Metric.isBounded_closedBall
  have hfin := (finite_latticePoints_of_isBounded ha hB).prod
    ((finite_univ (α := Fin 4)).prod (finite_univ (α := Fin 4)))
  refine Set.Finite.of_finite_image
    (f := fun p : ElementaryPlaquette a => (p.corner, p.lowAxis, p.highAxis))
    (hfin.subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨?_, mem_univ _, mem_univ _⟩
    have h1 : ‖p.center‖ ≤ R := mem_closedBall_zero_iff.mp (hR hp)
    have e : (p.corner : AmbientSpace) =
        p.center - Pi.single p.lowAxis (a / 2) - Pi.single p.highAxis (a / 2) := by
      simp only [ElementaryPlaquette.center]
      abel
    have n1 : ‖(Pi.single p.lowAxis (a / 2) : AmbientSpace)‖ = a / 2 := by
      rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have n2 : ‖(Pi.single p.highAxis (a / 2) : AmbientSpace)‖ = a / 2 := by
      rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith)]
    change (p.corner : AmbientSpace) ∈ Metric.closedBall (0 : AmbientSpace) (R + a)
    rw [mem_closedBall_zero_iff, e]
    have h2 := norm_sub_le (p.center - Pi.single p.lowAxis (a / 2))
      (Pi.single p.highAxis (a / 2) : AmbientSpace)
    have h3 := norm_sub_le p.center (Pi.single p.lowAxis (a / 2) : AmbientSpace)
    linarith
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext h.1 h.2.1 h.2.2
theorem finite_plaquettes_center_ne_zero {v : AmbientSpace → ℂ} (ha : 0 < a)
    (hv : IsBoundedBorelCompactlySupported v) :
    {p : ElementaryPlaquette a | v p.center ≠ 0}.Finite :=
  (finite_plaquettes_center_mem ha hv.2.2.isCompact.isBounded).subset
    fun _ hp => subset_tsupport v hp
theorem smearedEnergy_eq_sum (v : AmbientSpace → ℂ) {t : Finset (ElementaryPlaquette a)}
    (ht : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 → p ∈ t) (U : GaugeField a) :
    smearedEnergy v U = ∑ p ∈ t, v p.center * faceFunction p U := by
  rw [smearedEnergy, finsum_eq_sum_of_support_subset (s := t)]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.real_smul, mul_comm]
    rfl
  · intro p hp
    exact ht p fun h => hp (by simp [h])
theorem continuous_smearedEnergy {v : AmbientSpace → ℂ} (ha : 0 < a)
    (hv : IsBoundedBorelCompactlySupported v) :
    Continuous (smearedEnergy v : GaugeField a → ℂ) := by
  have e : (smearedEnergy v : GaugeField a → ℂ) = fun U =>
      ∑ p ∈ (finite_plaquettes_center_ne_zero ha hv).toFinset, v p.center * faceFunction p U :=
    funext (smearedEnergy_eq_sum v fun p hp =>
      (finite_plaquettes_center_ne_zero ha hv).mem_toFinset.mpr hp)
  rw [e]
  exact continuous_finset_sum _ fun p _ => continuous_const.mul (continuous_faceFunction p)
theorem smearedEnergy_dependsOnlyOnLinks {v : AmbientSpace → ℂ} (ha : 0 < a)
    (hv : IsBoundedBorelCompactlySupported v) {K : Set (Link a)}
    (h : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 → ∀ b ∈ edgeList p, b ∈ K) :
    DependsOnlyOnLinks K (smearedEnergy v : GaugeField a → ℂ) := by
  intro U V hUV
  have ht : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 →
      p ∈ (finite_plaquettes_center_ne_zero ha hv).toFinset :=
    fun p hp => (finite_plaquettes_center_ne_zero ha hv).mem_toFinset.mpr hp
  rw [smearedEnergy_eq_sum v ht U, smearedEnergy_eq_sum v ht V]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [faceFunction_dependsOnlyOnLinks p
    (h p ((finite_plaquettes_center_ne_zero ha hv).mem_toFinset.mp hp)) U V hUV]
theorem faceFunctionProperties (ha : 0 < a) : FaceFunctionProperties a := by
  have hside : ∀ p : ElementaryPlaquette a, {b | b ∈ edgeList p}.Finite :=
    fun p => List.finite_toSet _
  refine ⟨fun p => ⟨?_, fun U => faceEnergy_mem_Icc _ p, fun S hS => ?_⟩,
    fun Q hQ => finite_plaquettes_center_mem ha hQ, fun v hv => ?_, fun v w hv hw => ?_,
    fun z v hv => ?_⟩
  · exact mem_continuousFiniteLinkFunctions_of_dependsOnlyOnLinks ha (hside p)
      (fun b hb => mem_positiveLinks_of_mem_edgeList p hb)
      (continuous_faceFunction p) (faceFunction_dependsOnlyOnLinks p fun b hb => hb)
  · exact mem_regionObservables_of_dependsOnlyOnLinks ha
      (isBoundedObservable_of_continuous ha (continuous_faceFunction p))
      (faceFunction_dependsOnlyOnLinks p fun b hb => mem_positiveLinksWithin_of_mem_edgeList hS hb)
  · have hP := finite_plaquettes_center_ne_zero (a := a) ha hv
    have hc := continuous_smearedEnergy (a := a) ha hv
    have hE : Continuous (Complex.exp ∘ (smearedEnergy v : GaugeField a → ℂ)) :=
      Complex.continuous_exp.comp hc
    have hfin : (⋃ p ∈ {p : ElementaryPlaquette a | v p.center ≠ 0},
        {b | b ∈ edgeList p}).Finite :=
      hP.biUnion fun p _ => hside p
    have hpos : (⋃ p ∈ {p : ElementaryPlaquette a | v p.center ≠ 0}, {b | b ∈ edgeList p}) ⊆
        positiveLinkSet a := by
      intro b hb
      obtain ⟨p, -, hb⟩ := mem_iUnion₂.mp hb
      exact mem_positiveLinks_of_mem_edgeList p hb
    have hag : DependsOnlyOnLinks
        (⋃ p ∈ {p : ElementaryPlaquette a | v p.center ≠ 0}, {b | b ∈ edgeList p})
        (smearedEnergy v : GaugeField a → ℂ) :=
      smearedEnergy_dependsOnlyOnLinks ha hv fun p hp b hb => mem_iUnion₂.mpr ⟨p, hp, hb⟩
    refine ⟨?_, ?_, ?_, fun S hS => ?_⟩
    · exact hP.subset fun p hp h0 => hp (by simp only [h0, zero_smul])
    · exact mem_continuousFiniteLinkFunctions_of_dependsOnlyOnLinks ha hfin hpos hc hag
    · exact mem_continuousFiniteLinkFunctions_of_dependsOnlyOnLinks ha hfin hpos hE
        fun U V h => congrArg Complex.exp (hag U V h)
    · have hag' : DependsOnlyOnLinks (positiveLinksWithin a S)
          (smearedEnergy v : GaugeField a → ℂ) :=
        smearedEnergy_dependsOnlyOnLinks ha hv fun p hp b hb =>
          mem_positiveLinksWithin_of_mem_edgeList (hS p hp) hb
      exact ⟨mem_regionObservables_of_dependsOnlyOnLinks ha
          (isBoundedObservable_of_continuous ha hc) hag',
        mem_regionObservables_of_dependsOnlyOnLinks ha (isBoundedObservable_of_continuous ha hE)
          fun U V h => congrArg Complex.exp (hag' U V h)⟩
  · funext U
    classical
    let t : Finset (ElementaryPlaquette a) :=
      (finite_plaquettes_center_ne_zero ha hv).toFinset ∪
        (finite_plaquettes_center_ne_zero ha hw).toFinset
    have htv : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 → p ∈ t := fun p hp =>
      Finset.mem_union_left _ ((finite_plaquettes_center_ne_zero ha hv).mem_toFinset.mpr hp)
    have htw : ∀ p : ElementaryPlaquette a, w p.center ≠ 0 → p ∈ t := fun p hp =>
      Finset.mem_union_right _ ((finite_plaquettes_center_ne_zero ha hw).mem_toFinset.mpr hp)
    have ht : ∀ p : ElementaryPlaquette a, (v + w) p.center ≠ 0 → p ∈ t := by
      intro p hp
      by_contra hn
      have h1 : v p.center = 0 := by
        by_contra h
        exact hn (htv p h)
      have h2 : w p.center = 0 := by
        by_contra h
        exact hn (htw p h)
      exact hp (by simp [h1, h2])
    rw [Pi.add_apply, smearedEnergy_eq_sum (v + w) ht, smearedEnergy_eq_sum v htv,
      smearedEnergy_eq_sum w htw, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.add_apply]
    ring
  · funext U
    have ht : ∀ p : ElementaryPlaquette a, v p.center ≠ 0 →
        p ∈ (finite_plaquettes_center_ne_zero ha hv).toFinset := fun p hp =>
      (finite_plaquettes_center_ne_zero ha hv).mem_toFinset.mpr hp
    have ht' : ∀ p : ElementaryPlaquette a, (z • v) p.center ≠ 0 →
        p ∈ (finite_plaquettes_center_ne_zero ha hv).toFinset := by
      intro p hp
      refine ht p fun h => hp ?_
      simp [h]
    rw [Pi.smul_apply, smearedEnergy_eq_sum (z • v) ht', smearedEnergy_eq_sum v ht,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
theorem linkFunctionsStatement_holds (hSpace : CompactFieldsAndMeasures) :
    LinkFunctionsStatement := by
  intro a ha L hL
  obtain ⟨⟨-, -, -, -, -, hmet, -, -⟩, ⟨-, -, -, -, hdense⟩, -, -⟩ := hSpace a ha
  exact ⟨linkSpaceStructure ha hL, linkSupportCharacterizations ha hL,
    regionObservablesProperties ha L, boundedRegionFiniteness ha,
    boundedLimitClassProperty ha hmet hdense, faceFunctionProperties ha⟩
end FieldsAtSpacing.LinkFunctions
end YangMills.Construction
