import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLatticeProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservablesProof
import YangMills.Construction.InfiniteLattice.TorusLimitsArePeriodicGibbsStatesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace GibbsAtFixedSpacing.LinkFunctions
variable {a : ℝ}
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
section Values
variable {E : Set (Link a)} (h : HasNoOppositePairs E) (V : LinkVariables E)
  (U : GaugeField a)
theorem overwriteLinks_of_mem {b : Link a} (hb : b ∈ E) : overwriteLinks h V U b = V ⟨b, hb⟩ :=
  dif_pos hb
theorem overwriteLinks_of_notMem {b : Link a} (hb : b ∉ E) (hr : b.opposite ∉ E) :
    overwriteLinks h V U b = U b :=
  (dif_neg hb).trans (dif_neg hr)
theorem restrictField_overwriteLinks : restrictField (overwriteLinks h V U) E = V :=
  funext fun b => overwriteLinks_of_mem h V U b.2
theorem continuous_overwriteLinks :
    Continuous fun q : LinkVariables E × GaugeField a => overwriteLinks h q.1 q.2 := by apply _root_.YangMills.Construction.InfiniteLattice.ConfigurationSpace.continuous_overwriteLinks <;> assumption
theorem continuous_overwriteLinks_trivialField :
    Continuous fun V : LinkVariables E => overwriteLinks h V (trivialField a) :=
  (continuous_overwriteLinks h).comp (continuous_id.prodMk continuous_const)
end Values
theorem comap_pi_le_of_coords {Ω ι : Type*} (m : MeasurableSpace Ω)
    (g : Ω → ι → Matrices.ComplexMatrix2.specialUnitary)
    (h : ∀ i, MeasurableSpace.comap (fun x => g x i) inferInstance ≤ m) :
    MeasurableSpace.comap g MeasurableSpace.pi ≤ m :=
  (measurable_pi_iff.mpr fun i => measurable_iff_comap_le.mpr (h i)).comap_le
theorem linkSigma_eq_comap_restrictField (E : Set (Link a)) :
    linkSigma E = MeasurableSpace.comap (fun U : GaugeField a => restrictField U E)
      MeasurableSpace.pi := by
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    have h : (fun U : GaugeField a => U b) =
        (fun V : LinkVariables E => V ⟨b, hb⟩) ∘ fun U => restrictField U E := rfl
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply (⟨b, hb⟩ : E)).comap_le
  · exact comap_pi_le_of_coords _ _ fun b => le_iSup₂_of_le b.1 b.2 le_rfl
theorem borel_linkVariables (E : Set (Link a)) :
    borel (LinkVariables E) = MeasurableSpace.pi := by
  have := secondCountableTopology_specialUnitary
  exact (Pi.borelSpace (X := fun _ : E => Matrices.ComplexMatrix2.specialUnitary)).measurable_eq.symm
theorem linkSigma_le (E : Set (Link a)) :
    linkSigma E ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.SymmetryActionProof.linkSigma_le_borel <;> assumption
theorem linkSigma_mono {E E' : Set (Link a)} (h : E ⊆ E') : linkSigma E ≤ linkSigma E' := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.linkSigma_mono <;> assumption
theorem regionSigma_eq_linkSigma (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      linkSigma (positiveLinksWithin a S) := by apply _root_.YangMills.Construction.InfiniteLattice.ConfigurationSpace.regionSigma_eq_linkSigma <;> assumption
theorem isHomeomorph_restrictField (ha : 0 < a) :
    IsHomeomorph (fun U : GaugeField a => restrictField U (positiveLinkSet a)) := by apply _root_.YangMills.Construction.FixedSpacing.BasicFactsProof.isHomeomorph_restrictField <;> assumption
theorem borel_eq_linkSigma (ha : 0 < a) :
    borel (GaugeField a) = linkSigma (positiveLinkSet a) := by
  have hind := (isHomeomorph_restrictField ha).isEmbedding.isInducing
  have h : borel (GaugeField a) = @borel _ (TopologicalSpace.induced
      (fun U : GaugeField a => restrictField U (positiveLinkSet a))
      inferInstance) := congrArg (@borel _) hind.eq_induced
  rw [h, borel_comap, borel_linkVariables, linkSigma_eq_comap_restrictField]
theorem fieldsAreLinkFamilies (ha : 0 < a) : FieldsAreLinkFamilies a := by
  have hun : positiveLinksWithin a univ = positiveLinkSet a := by
    refine inter_eq_left.mpr fun b _ => ?_
    exact ⟨mem_univ _, mem_univ _⟩
  refine ⟨isHomeomorph_restrictField ha, fun E h => continuous_overwriteLinks h,
    borel_eq_linkSigma ha, ?_, regionSigma_eq_linkSigma⟩
  rw [regionSigma_eq_linkSigma, hun]
theorem dependsOnlyOnLinks_of_measurable {E : Set (Link a)} {F : GaugeField a → ℂ}
    (hF : Measurable[linkSigma E] F) : DependsOnlyOnLinks E F := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsOfTorusLimits.dependsOnlyOnLinks_of_measurable <;> assumption
section Factor
variable {E : Set (Link a)} (h : HasNoOppositePairs E)
include h
theorem measurable_overwriteLinks_trivialField {F : GaugeField a → ℂ} (hF : Measurable F) :
    Measurable fun V : LinkVariables E => F (overwriteLinks h V (trivialField a)) := by
  have := secondCountableTopology_specialUnitary
  exact hF.comp (continuous_overwriteLinks_trivialField h).measurable
theorem eq_overwriteLinks_restrictField {F : GaugeField a → ℂ} (hf : DependsOnlyOnLinks E F)
    (U : GaugeField a) :
    F U = F (overwriteLinks h (restrictField U E) (trivialField a)) :=
  hf _ _ (restrictField_overwriteLinks h _ _).symm
theorem measurable_of_dependsOnlyOnLinks {F : GaugeField a → ℂ} (hF : Measurable F)
    (hf : DependsOnlyOnLinks E F) : Measurable[linkSigma E] F := by
  have e : F = (fun V : LinkVariables E => F (overwriteLinks h V (trivialField a))) ∘
      fun U : GaugeField a => restrictField U E := funext (eq_overwriteLinks_restrictField h hf)
  rw [linkSigma_eq_comap_restrictField, e]
  exact (measurable_overwriteLinks_trivialField h hF).comp (comap_measurable _)
end Factor
theorem linkMeasurableFactorization (ha : 0 < a) : LinkMeasurableFactorization ha := by
  intro E hS F ⟨C, hC⟩
  have hh := hasNoOppositePairs_of_subset_positiveLinks ha hS
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := fun hF =>
      ⟨hF.mono (linkSigma_le E) le_rfl, dependsOnlyOnLinks_of_measurable hF⟩
    tfae_have 2 → 3 := fun ⟨hF, hf⟩ => by
      refine ⟨fun V => F (overwriteLinks hh V (trivialField a)), ?_, ⟨C, fun V => hC _⟩,
        eq_overwriteLinks_restrictField hh hf⟩
      rw [borel_linkVariables]
      exact measurable_overwriteLinks_trivialField hh hF
    tfae_have 3 → 1 := fun ⟨f, hf, _, he⟩ => by
      rw [borel_linkVariables] at hf
      have e : F = f ∘ fun U : GaugeField a => restrictField U E := funext he
      rw [linkSigma_eq_comap_restrictField, e]
      exact hf.comp (comap_measurable _)
    tfae_finish
  · intro f ⟨_, _, he⟩
    have hfill : ∀ V, f V = F (overwriteLinks hh V (trivialField a)) := fun V => by
      rw [he, restrictField_overwriteLinks]
    have hsurj : Function.Surjective fun U : GaugeField a => restrictField U E := fun V =>
      ⟨overwriteLinks hh V (trivialField a), restrictField_overwriteLinks hh V _⟩
    refine ⟨hfill, ?_, fun hc => ?_⟩
    · have e : (fun U => ‖F U‖) = (fun V => ‖f V‖) ∘
          fun U : GaugeField a => restrictField U E := funext fun U => by
        simp only [Function.comp_apply]
        rw [he]
      unfold observableSupNorm
      rw [e]
      exact (hsurj.iSup_comp fun V => ‖f V‖).symm
    · have e : f = fun V => F (overwriteLinks hh V (trivialField a)) := funext hfill
      rw [e]
      exact hc.comp (continuous_overwriteLinks_trivialField hh)
theorem finite_latticePoints_of_isBounded (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite := by apply _root_.YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof.finite_latticePoints_of_isBounded <;> assumption
theorem finite_positiveLinksWithin (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : (positiveLinksWithin a S).Finite := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeGeometry.finite_positiveLinksWithin <;> assumption
theorem dependsOnlyOnLinks_of_isRegionMeasurable {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) : DependsOnlyOnLinks (positiveLinksWithin a S) F := by
  refine dependsOnlyOnLinks_of_measurable ?_
  rw [← regionSigma_eq_linkSigma]
  exact hF
theorem isRegionMeasurable_of_dependsOnlyOnLinks (ha : 0 < a) {S : Set AmbientSpace}
    {E : Set (Link a)} (hS : E ⊆ positiveLinksWithin a S) {F : GaugeField a → ℂ}
    (hF : Measurable F) (hf : DependsOnlyOnLinks E F) : IsRegionMeasurable S F := by
  have hh := hasNoOppositePairs_of_subset_positiveLinks ha (hS.trans inter_subset_left)
  have hm := measurable_of_dependsOnlyOnLinks hh hF hf
  unfold IsRegionMeasurable
  rw [regionSigma_eq_linkSigma]
  exact hm.mono (linkSigma_mono hS) le_rfl
theorem isLocalObservable_iff_isCylinderFunction (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsLocalObservable F ↔ IsCylinderFunction F := by
  constructor
  · rintro ⟨S, hb, hm⟩
    exact ⟨_, finite_positiveLinksWithin ha hb, inter_subset_left,
      dependsOnlyOnLinks_of_isRegionMeasurable hm⟩
  · rintro ⟨W, hfin, hW, hf⟩
    let S : Set AmbientSpace := (fun b : Link a => (b.initial : AmbientSpace)) '' W ∪
      (fun b : Link a => (b.terminal : AmbientSpace)) '' W
    have hSfin : S.Finite := (hfin.image _).union (hfin.image _)
    refine ⟨S, hSfin.isBounded, isRegionMeasurable_of_dependsOnlyOnLinks ha ?_ hF.1 hf⟩
    intro b hb
    exact ⟨hW hb, Or.inl ⟨b, hb, rfl⟩, Or.inr ⟨b, hb, rfl⟩⟩
theorem overwriteLinks_singleton_of_ne (ha : 0 < a) {b c : Link a}
    (hb : b ∈ positiveLinkSet a) (hc : c ∈ positiveLinkSet a) (hne : c ≠ b)
    (V : LinkVariables ({b} : Set (Link a))) (U : GaugeField a) :
    overwriteLinks (hasNoOppositePairs_singleton ha b) V U c = U c := by
  refine overwriteLinks_of_notMem _ _ _ hne fun hr => ?_
  have hr' : c.opposite = b := hr
  exact opposite_notMem_positiveLinks ha hc (hr' ▸ hb)
theorem not_dependsOnLink (ha : 0 < a) {E : Set (Link a)} (hS : E ⊆ positiveLinkSet a)
    {F : GaugeField a → ℂ} (hf : DependsOnlyOnLinks E F) {b : Link a}
    (hb : b ∈ positiveLinkSet a) (hbS : b ∉ E) : ¬ DependsOnLink ha F b := by
  refine not_not.mpr fun V U => hf _ _ (funext fun c => ?_)
  exact overwriteLinks_singleton_of_ne ha hb (hS c.2) (fun e => hbS (e ▸ c.2)) V U
theorem eq_of_eq_off_finset (ha : 0 < a) {E : Set (Link a)} (hS : E ⊆ positiveLinkSet a)
    {F : GaugeField a → ℂ} (hf : DependsOnlyOnLinks E F) (T : Finset (Link a)) :
    (∀ b ∈ T, b ∈ positiveLinkSet a ∧ ¬ DependsOnLink ha F b) →
      ∀ U U' : GaugeField a, (∀ c ∈ E, c ∉ T → U c = U' c) → F U = F U' := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ U U' h
    exact hf _ _ (funext fun c => h c.1 c.2 (by simp))
  | insert b T _ ih =>
    intro hT U U' h
    obtain ⟨hbB, hbr⟩ := hT b (Finset.mem_insert_self b T)
    have hnr : IsIndependentOfLinks (hasNoOppositePairs_singleton ha b) F := not_not.mp hbr
    let V : LinkVariables ({b} : Set (Link a)) := fun _ => U' b
    have h₁ : F (overwriteLinks (hasNoOppositePairs_singleton ha b) V U) = F U := hnr V U
    rw [← h₁]
    refine ih (fun c hc => hT c (Finset.mem_insert_of_mem hc)) _ _ fun c hc hcT => ?_
    by_cases hcb : c = b
    · rw [hcb]
      exact overwriteLinks_of_mem (hasNoOppositePairs_singleton ha b) V U (mem_singleton b)
    · rw [overwriteLinks_singleton_of_ne ha hbB (hS hc) hcb]
      exact h c hc (by simp [hcb, hcT])
theorem dependsOnlyOnLinks_linkSupport (ha : 0 < a) {E : Set (Link a)} (hfin : E.Finite)
    (hS : E ⊆ positiveLinkSet a) {F : GaugeField a → ℂ}
    (hf : DependsOnlyOnLinks E F) : DependsOnlyOnLinks (linkSupport ha F) F := by
  intro U U' h
  have hfin' : (E \ linkSupport ha F).Finite := hfin.subset sdiff_subset
  refine eq_of_eq_off_finset ha hS hf hfin'.toFinset (fun b hb => ?_) U U' fun c hc hcT => ?_
  · have hb' := hfin'.mem_toFinset.mp hb
    exact ⟨hS hb'.1, fun hr => hb'.2 ⟨hS hb'.1, hr⟩⟩
  · have hcs : c ∈ linkSupport ha F := by
      by_contra hn
      exact hcT (hfin'.mem_toFinset.mpr ⟨hc, hn⟩)
    exact congrFun h ⟨c, hcs⟩
theorem linkSupport_subset (ha : 0 < a) {E : Set (Link a)} (hS : E ⊆ positiveLinkSet a)
    {F : GaugeField a → ℂ} (hf : DependsOnlyOnLinks E F) : linkSupport ha F ⊆ E := by
  intro b hb
  by_contra hbS
  exact not_dependsOnLink ha hS hf hb.1 hbS hb.2
theorem localObservablesSupports (ha : 0 < a) : LocalObservablesSupports ha := by
  refine ⟨fun S hS => finite_latticePoints_of_isBounded ha hS,
    fun S hS => finite_positiveLinksWithin ha hS,
    fun F hF => isLocalObservable_iff_isCylinderFunction ha hF, ?_⟩
  intro F E _ hfin hS hf
  have hsupp := dependsOnlyOnLinks_linkSupport ha hfin hS hf
  refine ⟨linkSupport_subset ha hS hf, hsupp, fun E' h' hoff V U => ?_⟩
  refine hsupp _ _ (funext fun c => ?_)
  exact overwriteLinks_of_notMem h' V U (hoff c.1 c.2).1 (hoff c.1 c.2).2
theorem locallyMeasurableCharacterization (ha : 0 < a) :
    LocallyMeasurableCharacterization a := by
  intro S
  have hB : ∀ T : Set AmbientSpace,
      regionSigma (a := a) T ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    fun T => linkSigma_le _
  ext F
  simp only [locallyMeasurableIn, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨Q, hQ, hm, hC⟩
    have hF : Measurable F := hm.mono (hB _) le_rfl
    refine ⟨⟨hF, hC⟩, ⟨S ∩ Q, hQ.subset inter_subset_right, hm⟩, ?_⟩
    exact hm.mono (biSup_mono fun b hb => ⟨hb.1.1, hb.2.1⟩) le_rfl
  · rintro ⟨hF, ⟨Q, hQ, hmQ⟩, hmS⟩
    have hBQ : positiveLinksWithin a Q ⊆ positiveLinkSet a := inter_subset_left
    have hBS : positiveLinksWithin a S ⊆ positiveLinkSet a := inter_subset_left
    have hfQ := dependsOnlyOnLinks_of_isRegionMeasurable hmQ
    have hfS := dependsOnlyOnLinks_of_isRegionMeasurable hmS
    have hsupp := dependsOnlyOnLinks_linkSupport ha (finite_positiveLinksWithin ha hQ) hBQ hfQ
    have hsub : linkSupport ha F ⊆ positiveLinksWithin a (S ∩ Q) := by
      intro b hb
      have h₁ := linkSupport_subset ha hBQ hfQ hb
      have h₂ := linkSupport_subset ha hBS hfS hb
      exact ⟨hb.1, ⟨h₂.2.1, h₁.2.1⟩, ⟨h₂.2.2, h₁.2.2⟩⟩
    exact ⟨Q, hQ, isRegionMeasurable_of_dependsOnlyOnLinks ha hsub hF.1 hsupp, hF.2⟩
theorem assertion_holds : Assertion := fun _ ha =>
  ⟨fieldsAreLinkFamilies ha, linkMeasurableFactorization ha, localObservablesSupports ha,
    locallyMeasurableCharacterization ha⟩
end GibbsAtFixedSpacing.LinkFunctions
end YangMills.Construction
