import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservablesProof
import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunctionProof
import YangMills.Construction.InfiniteLattice.CountableProductsOfCopiesOfTheGroup
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBondsProof
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservablesProof
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoffProof
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ConfigurationSpace
variable {a : ℝ}
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_of_forall_link {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
theorem continuous_gluedField (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) (ω : GaugeField a) :
    Continuous fun V : LinkVariables S => gluedField ha hS V ω := by
  refine continuous_of_forall_link fun b => ?_
  classical
  by_cases h : b ∈ S
  · have e : (fun V : LinkVariables S => gluedField ha hS V ω b) = fun V => V ⟨b, h⟩ :=
      funext fun V => dif_pos h
    rw [e]
    exact continuous_apply _
  · by_cases h' : b.opposite ∈ S
    · have e : (fun V : LinkVariables S => gluedField ha hS V ω b) =
          fun V => (V ⟨b.opposite, h'⟩)⁻¹ :=
        funext fun V => (dif_neg h).trans (dif_pos h')
      rw [e]
      exact (continuous_apply _).inv
    · have e : (fun V : LinkVariables S => gluedField ha hS V ω b) = fun _ => ω b :=
        funext fun V => (dif_neg h).trans (dif_neg h')
      rw [e]
      exact continuous_const
def positiveLinksHomeomorph (ha : 0 < a) :
    GaugeField a ≃ₜ LinkVariables (positiveLinkSet a) where
  toFun U := restrictField U (positiveLinkSet a)
  invFun g := gluedField ha subset_rfl g (trivialField a)
  left_inv U := (eq_gluedField ha subset_rfl _ (trivialField a) U (fun _ => rfl)
    (fun _ hb => (hb.2 hb.1).elim)).symm
  right_inv g := funext fun b => gluedField_apply_of_mem ha subset_rfl g _ b
  continuous_toFun := continuous_pi fun b => continuous_eval_link b.1
  continuous_invFun := continuous_gluedField ha subset_rfl _
theorem compactSpace_gaugeField (ha : 0 < a) : CompactSpace (GaugeField a) :=
  (positiveLinksHomeomorph ha).symm.compactSpace
theorem isBoundedObservable_of_continuous (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : Continuous F) : IsBoundedObservable F := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperatorPropertiesProof.isBoundedObservable_of_continuous <;> assumption
theorem borel_measurable_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) : @Measurable X Y (borel X) (borel Y) f := by apply _root_.YangMills.Construction.InfiniteLattice.LinkSetFunctions.continuous_measurable_borel <;> assumption
theorem borel_linkVariables_eq_iSup (hprod : CountableProductTheorem)
    (𝓜 : Set (Link a)) :
    borel (LinkVariables 𝓜) =
      ⨆ j : 𝓜, (borel ComplexMatrix2.specialUnitary).comap fun g : LinkVariables 𝓜 => g j :=
  (hprod.1 𝓜 ((isAtMostCountable_iff_countable _).mpr inferInstance)).2.1.2
theorem measurable_restrictField (hprod : CountableProductTheorem)
    (𝓜 : Set (Link a)) :
    @Measurable _ _ (linkSigma 𝓜) (borel (LinkVariables 𝓜))
      (fun U : GaugeField a => restrictField U 𝓜) := by
  rw [borel_linkVariables_eq_iSup hprod 𝓜, measurable_iff_comap_le, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂_of_le (f := fun b (_ : b ∈ 𝓜) =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) j.1 j.2 le_rfl
theorem borel_eq_linkSigma_positiveLinks (ha : 0 < a)
    (hprod : CountableProductTheorem) :
    borel (GaugeField a) = linkSigma (positiveLinkSet a) := by
  have h₁ : borel (GaugeField a) =
      (borel (LinkVariables (positiveLinkSet a))).comap (positiveLinksHomeomorph ha) := by
    have h := @borel_comap _ _ (positiveLinksHomeomorph ha) inferInstance
    rwa [← (positiveLinksHomeomorph ha).isInducing.eq_induced] at h
  rw [h₁, borel_linkVariables_eq_iSup hprod, MeasurableSpace.comap_iSup, linkSigma, iSup_subtype']
  refine iSup_congr fun j => ?_
  rw [MeasurableSpace.comap_comp]
  have e : (fun g : LinkVariables (positiveLinkSet a) => g j) ∘ ⇑(positiveLinksHomeomorph ha) =
      fun U : GaugeField a => U j.1 := rfl
  have e₂ : borel ComplexMatrix2.specialUnitary =
      (inferInstance : MeasurableSpace ComplexMatrix2.specialUnitary) :=
    BorelSpace.measurable_eq.symm
  rw [e, e₂]
theorem borel_eq_linkSigma_univ (ha : 0 < a)
    (hprod : CountableProductTheorem) :
    borel (GaugeField a) = linkSigma (univ : Set (Link a)) := by
  refine le_antisymm ?_ ?_
  · rw [borel_eq_linkSigma_positiveLinks ha hprod]
    exact iSup₂_le fun b _ => le_iSup₂_of_le (f := fun b (_ : b ∈ (univ : Set (Link a))) =>
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b (mem_univ b) le_rfl
  · refine iSup₂_le fun b _ => ?_
    exact (continuous_eval_link b).measurable.comap_le
@[reducible] def saturatedSigma (𝓜 : Set (Link a)) : MeasurableSpace (GaugeField a) where
  MeasurableSet' B := ∀ U U' : GaugeField a,
    restrictField U 𝓜 = restrictField U' 𝓜 → U ∈ B → U' ∈ B
  measurableSet_empty := fun _ _ _ h => h
  measurableSet_compl B hB U U' h hU hU' := hU (hB U' U h.symm hU')
  measurableSet_iUnion f hf U U' h hU := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hU
    exact mem_iUnion.mpr ⟨i, hf i U U' h hi⟩
theorem linkSigma_le_saturatedSigma (𝓜 : Set (Link a)) :
    linkSigma 𝓜 ≤ saturatedSigma 𝓜 := by
  refine iSup₂_le fun b hb => ?_
  rintro _ ⟨E, _, rfl⟩ U U' h hU
  have e : U b = U' b := congrFun h ⟨b, hb⟩
  change U' b ∈ E
  rw [← e]
  exact hU
theorem eq_of_measurable_of_restrict_eq {𝓜 : Set (Link a)} {H : GaugeField a → ℂ}
    (hH : Measurable[linkSigma 𝓜] H) (U U' : GaugeField a)
    (h : restrictField U 𝓜 = restrictField U' 𝓜) : H U = H U' := by
  have hs : MeasurableSet[linkSigma 𝓜] (H ⁻¹' {H U}) := hH (measurableSet_singleton _)
  have hm : U' ∈ H ⁻¹' {H U} := linkSigma_le_saturatedSigma 𝓜 _ hs U U' h rfl
  exact (mem_singleton_iff.mp hm).symm
def extendByOne (ha : 0 < a) {𝓜 : Set (Link a)} (hM : 𝓜 ⊆ positiveLinkSet a)
    (g : LinkVariables 𝓜) : GaugeField a :=
  gluedField ha hM g (trivialField a)
theorem restrictField_extendByOne (ha : 0 < a) {𝓜 : Set (Link a)}
    (hM : 𝓜 ⊆ positiveLinkSet a) (g : LinkVariables 𝓜) :
    restrictField (extendByOne ha hM g) 𝓜 = g :=
  funext fun b => gluedField_apply_of_mem ha hM g _ b
theorem continuous_extendByOne (ha : 0 < a) {𝓜 : Set (Link a)}
    (hM : 𝓜 ⊆ positiveLinkSet a) : Continuous (extendByOne ha hM) :=
  continuous_gluedField ha hM _
theorem comp_extendByOne_mem_boundedBorel (ha : 0 < a) {𝓜 : Set (Link a)}
    (hM : 𝓜 ⊆ positiveLinkSet a) {H : GaugeField a → ℂ} (hH : IsBoundedObservable H) :
    H ∘ extendByOne ha hM ∈ boundedBorelSpace (LinkVariables 𝓜) := by
  obtain ⟨hm, C, hC⟩ := hH
  refine ⟨?_, C, fun g => hC _⟩
  exact hm.comp (borel_measurable_of_continuous (continuous_extendByOne ha hM))
theorem eq_comp_extendByOne_restrict (ha : 0 < a) {𝓜 : Set (Link a)}
    (hM : 𝓜 ⊆ positiveLinkSet a) {H : GaugeField a → ℂ}
    (hr : ∀ U U' : GaugeField a, restrictField U 𝓜 = restrictField U' 𝓜 → H U = H U')
    (U : GaugeField a) : H U = (H ∘ extendByOne ha hM) (restrictField U 𝓜) :=
  hr _ _ (restrictField_extendByOne ha hM _).symm
theorem measurable_of_eq_comp_restrictField (hprod : CountableProductTheorem)
    {𝓜 : Set (Link a)} {H : GaugeField a → ℂ} {h : LinkVariables 𝓜 → ℂ}
    (hh : h ∈ boundedBorelSpace (LinkVariables 𝓜))
    (e : ∀ U : GaugeField a, H U = h (restrictField U 𝓜)) :
    Measurable[linkSigma 𝓜] H := by
  have hc : H = h ∘ fun U : GaugeField a => restrictField U 𝓜 := funext e
  rw [hc]
  exact fun s hs => measurable_restrictField hprod 𝓜 (hh.1 hs)
theorem measurable_of_restrict_invariant (ha : 0 < a) (hprod : CountableProductTheorem)
    {𝓜 : Set (Link a)} (hM : 𝓜 ⊆ positiveLinkSet a) {H : GaugeField a → ℂ}
    (hH : IsBoundedObservable H)
    (hr : ∀ U U' : GaugeField a, restrictField U 𝓜 = restrictField U' 𝓜 → H U = H U') :
    Measurable[linkSigma 𝓜] H :=
  measurable_of_eq_comp_restrictField hprod (comp_extendByOne_mem_boundedBorel ha hM hH)
    (eq_comp_extendByOne_restrict ha hM hr)
theorem regionSigma_eq_linkSigma (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)) =
      linkSigma (positiveLinksWithin a S) := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun c hc => ?_
    rcases mem_positiveLinks_or_opposite_mem c with h | h
    · exact le_iSup₂_of_le (f := fun b (_ : b ∈ positiveLinksWithin a S) =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) c ⟨h, hc⟩ le_rfl
    · have hr : c.opposite ∈ positiveLinksWithin a S := ⟨h, hc.2, hc.1⟩
      refine le_trans ?_ (le_iSup₂_of_le (f := fun b (_ : b ∈ positiveLinksWithin a S) =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) c.opposite hr le_rfl)
      have e : (fun U : GaugeField a => U c) =
          (fun g : ComplexMatrix2.specialUnitary => g⁻¹) ∘ fun U : GaugeField a => U c.opposite :=
        funext fun U => U.2 c.opposite
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono continuous_inv.measurable.comap_le
  · exact iSup₂_le fun b hb => le_iSup₂_of_le (f := fun b (_ : b ∈ linksWithin S) =>
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b hb.2 le_rfl
theorem linkSigma_mono {𝓜 𝓜' : Set (Link a)} (h : 𝓜 ⊆ 𝓜') :
    (linkSigma 𝓜 : MeasurableSpace (GaugeField a)) ≤ linkSigma 𝓜' := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.linkSigma_mono <;> assumption
theorem isLocalObservable_iff (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      (positiveLinksWithin a S).Finite) (A : GaugeField a → ℂ) :
    IsLocalObservable A ↔ ∃ 𝓜 : Set (Link a), 𝓜.Finite ∧ 𝓜 ⊆ positiveLinkSet a ∧
      Measurable[linkSigma 𝓜] A := by
  constructor
  · rintro ⟨S, hS, hA⟩
    refine ⟨_, hfin S hS, inter_subset_left, ?_⟩
    rw [← regionSigma_eq_linkSigma]
    exact hA
  · rintro ⟨𝓜, hM, hB, hA⟩
    let T : Set AmbientSpace :=
      (fun x : LatticePoint a => (x : AmbientSpace)) '' (Link.initial '' 𝓜 ∪ Link.terminal '' 𝓜)
    have hT : T.Finite := ((hM.image _).union (hM.image _)).image _
    refine ⟨T, hT.isBounded, ?_⟩
    have hle : (linkSigma 𝓜 : MeasurableSpace (GaugeField a)) ≤ regionSigma T := by
      rw [regionSigma_eq_linkSigma]
      refine linkSigma_mono fun b hb => ⟨hB hb, ?_, ?_⟩
      · exact ⟨b.initial, Or.inl ⟨b, hb, rfl⟩, rfl⟩
      · exact ⟨b.terminal, Or.inr ⟨b, hb, rfl⟩, rfl⟩
    exact hA.mono hle le_rfl
theorem isLocalObservable_add_mul (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      (positiveLinksWithin a S).Finite) {A B : GaugeField a → ℂ}
    (hA : IsBoundedObservable A) (hlA : IsLocalObservable A) (hB : IsBoundedObservable B)
    (hlB : IsLocalObservable B) :
    (IsBoundedObservable (A + B) ∧ IsLocalObservable (A + B)) ∧
      (IsBoundedObservable (A * B) ∧ IsLocalObservable (A * B)) := by
  obtain ⟨𝓜, hM, hMB, hmA⟩ := (isLocalObservable_iff hfin A).mp hlA
  obtain ⟨𝓜', hM', hMB', hmB⟩ := (isLocalObservable_iff hfin B).mp hlB
  have h₁ : Measurable[linkSigma (𝓜 ∪ 𝓜')] A :=
    hmA.mono (linkSigma_mono subset_union_left) le_rfl
  have h₂ : Measurable[linkSigma (𝓜 ∪ 𝓜')] B :=
    hmB.mono (linkSigma_mono subset_union_right) le_rfl
  obtain ⟨mA, C, hC⟩ := hA
  obtain ⟨mB, C', hC'⟩ := hB
  refine ⟨⟨⟨mA.add mB, C + C', fun U => ?_⟩, ?_⟩, ⟨⟨mA.mul mB, C * C', fun U => ?_⟩, ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (hC U) (hC' U))
  · refine (isLocalObservable_iff hfin _).mpr ⟨𝓜 ∪ 𝓜', hM.union hM', union_subset hMB hMB', ?_⟩
    exact h₁.add h₂
  · rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC U) (hC' U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  · refine (isLocalObservable_iff hfin _).mpr ⟨𝓜 ∪ 𝓜', hM.union hM', union_subset hMB hMB', ?_⟩
    exact h₁.mul h₂
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => faceEnergy U p := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.continuous_faceEnergy <;> assumption
theorem faceEnergy_mem_Icc (hlog : ComplexMatrix2.UnitaryLogarithmProperties) (U : GaugeField a)
    (p : ElementaryPlaquette a) : faceEnergy U p ∈ Icc (0 : ℝ) 2 := by
  obtain ⟨⟨t, ht, e⟩, -⟩ := hlog.2.1 (faceHolonomy U p : ComplexMatrix2) (faceHolonomy U p).2
  have h2 : ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2) = ((2 * t : ℝ) : ℂ) := by
    push_cast
    rw [← e]
    simp only [ComplexMatrix2.halfTrace]
    ring
  have : faceEnergy U p = 1 - t := by
    rw [faceEnergy, h2, Complex.ofReal_re]
    ring
  rw [this]
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
theorem faceEnergy_congr {p : ElementaryPlaquette a} {U U' : GaugeField a}
    (h : ∀ b ∈ p.edges, U b = U' b) : faceEnergy U p = faceEnergy U' p := by
  have h₁ := h (Link.forwardFrom p.corner p.lowAxis) (by simp [ElementaryPlaquette.edges])
  have h₂ := h (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)
    (by simp [ElementaryPlaquette.edges])
  have h₃ := h (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)
    (by simp [ElementaryPlaquette.edges])
  have h₄ := h (Link.forwardFrom p.corner p.highAxis) (by simp [ElementaryPlaquette.edges])
  simp only [faceEnergy, faceHolonomy, h₁, h₂, h₃, h₄]
theorem edges_subset_positiveLinks (p : ElementaryPlaquette a) :
    {b | b ∈ p.edges} ⊆ positiveLinkSet a := by
  intro b hb
  simp only [ElementaryPlaquette.edges, mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
theorem finite_faces_containing
    (hsix : ∀ b ∈ positiveLinkSet a, {p : ElementaryPlaquette a | b ∈ p.edges}.ncard = 6)
    (c : Link a) : {p : ElementaryPlaquette a | c ∈ p.edges}.Finite := by
  by_cases hc : c ∈ positiveLinkSet a
  · exact finite_of_ncard_ne_zero (by rw [hsix c hc]; norm_num)
  · convert finite_empty
    exact eq_empty_of_forall_notMem fun p hp => hc (edges_subset_positiveLinks p hp)
theorem finite_plaquettesTouching (ha : 0 < a)
    (hsix : ∀ b ∈ positiveLinkSet a, {p : ElementaryPlaquette a | b ∈ p.edges}.ncard = 6)
    (𝓛 : Finset (Link a)) : (plaquettesTouching 𝓛).Finite := by
  refine Set.Finite.subset (𝓛.finite_toSet.biUnion fun c _ =>
    (finite_faces_containing hsix c).union (finite_faces_containing hsix c.opposite)) ?_
  intro p hp
  obtain ⟨b, hb, h | h⟩ := (mem_plaquettesTouching_iff ha 𝓛 p).mp hp
  · exact mem_biUnion (Finset.mem_coe.mpr h) (Or.inl hb)
  · exact mem_biUnion (Finset.mem_coe.mpr h) (Or.inr hb)
theorem homeomorphPositiveLinks_holds (ha : 0 < a) (hprod : CountableProductTheorem) :
    HomeomorphPositiveLinks a := by
  have hc := (hprod.1 (positiveLinkSet a)
    ((isAtMostCountable_iff_countable _).mpr inferInstance)).1.1
  have := hc.2
  exact ⟨(positiveLinksHomeomorph ha).isHomeomorph, hc, compactSpace_gaugeField ha,
    (positiveLinksHomeomorph ha).isEmbedding.metrizableSpace⟩
theorem borelEqLinkSigma_holds (ha : 0 < a) (hprod : CountableProductTheorem) :
    BorelEqLinkSigma a :=
  ⟨borel_eq_linkSigma_univ ha hprod, borel_eq_linkSigma_positiveLinks ha hprod⟩
theorem measurableOnLinks_holds (ha : 0 < a)
    (hprod : CountableProductTheorem) :
    MeasurableOnLinksCharacterization a := by
  refine ⟨fun 𝓜 hM H hH => ⟨?_, ?_, ?_⟩, fun 𝓛 _ H hH => ⟨fun hm => ?_, ?_⟩⟩
  · tfae_have 1 → 2 := fun h U U' e => eq_of_measurable_of_restrict_eq h U U' e
    tfae_have 2 → 3 := fun h =>
      ⟨H ∘ extendByOne ha hM, comp_extendByOne_mem_boundedBorel ha hM hH,
        eq_comp_extendByOne_restrict ha hM h⟩
    tfae_have 3 → 1 := by
      rintro ⟨h, hh, e⟩
      exact measurable_of_eq_comp_restrictField hprod hh e
    tfae_finish
  · intro h _ h' _ e e'
    funext g
    have r := restrictField_extendByOne ha hM g
    calc h g = h (restrictField (extendByOne ha hM g) 𝓜) := by rw [r]
      _ = H (extendByOne ha hM g) := (e _).symm
      _ = h' (restrictField (extendByOne ha hM g) 𝓜) := e' _
      _ = h' g := by rw [r]
  · intro h _ e hc
    have hh : h = H ∘ extendByOne ha hM := funext fun g => by
      have r := restrictField_extendByOne ha hM g
      calc h g = h (restrictField (extendByOne ha hM g) 𝓜) := by rw [r]
        _ = H (extendByOne ha hM g) := (e _).symm
    rw [hh]
    exact hc.comp (continuous_extendByOne ha hM)
  · have hM : complementLinks 𝓛 ⊆ positiveLinkSet a := sdiff_subset
    exact ⟨H ∘ extendByOne ha hM, comp_extendByOne_mem_boundedBorel ha hM hH,
      eq_comp_extendByOne_restrict ha hM (eq_of_measurable_of_restrict_eq hm)⟩
  · rintro ⟨h, hh, e⟩
    exact measurable_of_eq_comp_restrictField hprod hh e
theorem linkSigmaAndLocality_holds (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      (positiveLinksWithin a S).Finite) :
    LinkSigmaAndLocality a :=
  ⟨regionSigma_eq_linkSigma, fun _ _ h _ => linkSigma_mono h,
    fun A _ => isLocalObservable_iff hfin A,
    fun _ _ hA hlA hB hlB => isLocalObservable_add_mul hfin hA hlA hB hlB⟩
theorem isLocalObservable_of_restrict_invariant (ha : 0 < a) (hprod : CountableProductTheorem)
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite)
    {𝓜 : Set (Link a)} (hM : 𝓜.Finite) (hB : 𝓜 ⊆ positiveLinkSet a)
    {H : GaugeField a → ℂ} (hH : IsBoundedObservable H)
    (hr : ∀ U U' : GaugeField a, restrictField U 𝓜 = restrictField U' 𝓜 → H U = H U') :
    IsLocalObservable H :=
  (isLocalObservable_iff hfin H).mpr ⟨𝓜, hM, hB, measurable_of_restrict_invariant ha hprod hB hH hr⟩
theorem faceEnergyAndBoltzmannWeight_holds (ha : 0 < a)
    (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hprod : CountableProductTheorem)
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite)
    (hends : ∀ p : ElementaryPlaquette a, ∀ b ∈ p.edges,
      b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet)
    (hsix : ∀ b ∈ positiveLinkSet a, {p : ElementaryPlaquette a | b ∈ p.edges}.ncard = 6) :
    FaceEnergyAndBoltzmannWeight a := by
  refine ⟨fun p => ⟨continuous_faceEnergy p, fun U => faceEnergy_mem_Icc hlog U p, ?_⟩,
    fun 𝓛 _ β hβ => ?_⟩
  · have hc : Continuous fun U : GaugeField a => (faceEnergy U p : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_faceEnergy p)
    have hm : Measurable[linkSigma {b | b ∈ p.edges}]
        (fun U : GaugeField a => (faceEnergy U p : ℂ)) :=
      measurable_of_restrict_invariant ha hprod (edges_subset_positiveLinks p)
        (isBoundedObservable_of_continuous ha hc)
        fun U U' e => congrArg _ (faceEnergy_congr fun b hb => congrFun e ⟨b, hb⟩)
    refine hm.mono ?_ le_rfl
    rw [regionSigma_eq_linkSigma]
    exact linkSigma_mono fun b hb => ⟨edges_subset_positiveLinks p hb,
      ⟨b.initial, (hends p b hb).1, rfl⟩, ⟨b.terminal, (hends p b hb).2, rfl⟩⟩
  · have hP := finite_plaquettesTouching ha hsix 𝓛
    have hW : ∀ U : GaugeField a, wilsonLinkEnergy β 𝓛 U =
        β * ∑ p ∈ hP.toFinset, faceEnergy U p := fun U => by
      rw [wilsonLinkEnergy, finsum_mem_eq_finite_toFinset_sum _ hP]
    have hWc : Continuous fun U : GaugeField a => wilsonLinkEnergy β 𝓛 U := by
      simp only [hW]
      exact continuous_const.mul (continuous_finsetSum _ fun p _ => continuous_faceEnergy p)
    have hW0 : ∀ U : GaugeField a, 0 ≤ wilsonLinkEnergy β 𝓛 U := fun U => by
      rw [hW]
      exact mul_nonneg hβ.le (Finset.sum_nonneg fun p _ => (faceEnergy_mem_Icc hlog U p).1)
    have hc : Continuous fun U : GaugeField a =>
        ((Real.exp (-wilsonLinkEnergy β 𝓛 U) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp hWc.neg)
    have hobs := isBoundedObservable_of_continuous ha hc
    let 𝓜 : Set (Link a) := ⋃ p ∈ hP.toFinset, {b | b ∈ p.edges}
    have hM : 𝓜.Finite := (Finset.finite_toSet _).biUnion fun p _ => List.finite_toSet p.edges
    have hB : 𝓜 ⊆ positiveLinkSet a := iUnion₂_subset fun p _ => edges_subset_positiveLinks p
    refine ⟨hP, ⟨hc, hobs, isLocalObservable_of_restrict_invariant ha hprod hfin hM hB hobs
      fun U U' e => ?_⟩, fun U =>
      ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hW0 U))⟩⟩
    have hs : wilsonLinkEnergy β 𝓛 U = wilsonLinkEnergy β 𝓛 U' := by
      rw [hW, hW]
      refine congrArg _ (Finset.sum_congr rfl fun p hp => faceEnergy_congr fun b hb => ?_)
      exact congrFun e ⟨b, mem_biUnion hp hb⟩
    simp only [hs]
theorem continuous_overwriteLinks {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢) :
    Continuous fun x : LinkVariables 𝓢 × GaugeField a => overwriteLinks h x.1 x.2 := by
  refine continuous_of_forall_link fun b => ?_
  classical
  by_cases hb : b ∈ 𝓢
  · have e : (fun x : LinkVariables 𝓢 × GaugeField a => overwriteLinks h x.1 x.2 b) =
        fun x => x.1 ⟨b, hb⟩ := funext fun x => dif_pos hb
    rw [e]
    exact (continuous_apply _).comp continuous_fst
  · by_cases hr : b.opposite ∈ 𝓢
    · have e : (fun x : LinkVariables 𝓢 × GaugeField a => overwriteLinks h x.1 x.2 b) =
          fun x => (x.1 ⟨b.opposite, hr⟩)⁻¹ := funext fun x => (dif_neg hb).trans (dif_pos hr)
      rw [e]
      exact ((continuous_apply _).comp continuous_fst).inv
    · have e : (fun x : LinkVariables 𝓢 × GaugeField a => overwriteLinks h x.1 x.2 b) =
          fun x => x.2 b := funext fun x => (dif_neg hb).trans (dif_neg hr)
      rw [e]
      exact (continuous_eval_link b).comp continuous_snd
theorem overwriteLinksProperties_holds : OverwriteLinksProperties a := by
  refine ⟨fun 𝓛 h => ⟨fun V U => ⟨overwriteLinks_apply_of_mem h V U,
    overwriteLinks_apply_opposite h V U,
    fun c hc hr => overwriteLinks_apply_of_not_mem h V U hc hr⟩, continuous_overwriteLinks h⟩, ?_⟩
  intro 𝓛 h _ V U U' hout
  refine Subtype.ext (funext fun c => ?_)
  by_cases hc : c ∈ (𝓛 : Set (Link a))
  · exact (overwriteLinks_apply_of_mem h V U ⟨c, hc⟩).trans
      (overwriteLinks_apply_of_mem h V U' ⟨c, hc⟩).symm
  · by_cases hr : c.opposite ∈ (𝓛 : Set (Link a))
    · exact (overwriteLinks_apply_opposite h V U ⟨c.opposite, hr⟩).trans
        (overwriteLinks_apply_opposite h V U' ⟨c.opposite, hr⟩).symm
    · refine (overwriteLinks_apply_of_not_mem h V U hc hr).trans
        (Eq.trans ?_ (overwriteLinks_apply_of_not_mem h V U' hc hr).symm)
      have hval : ∀ b ∈ positiveLinkSet a, b ∉ (𝓛 : Set (Link a)) → U b = U' b :=
        fun b hb hn => congrFun hout ⟨b, hb, hn⟩
      rcases mem_positiveLinks_or_opposite_mem c with h₁ | h₁
      · exact hval c h₁ hc
      · have e := hval _ h₁ hr
        calc U c = (U c.opposite)⁻¹ := U.2 c.opposite
          _ = (U' c.opposite)⁻¹ := by rw [e]
          _ = U' c := (U'.2 c.opposite).symm
theorem denseContinuousLocal_holds (ha : 0 < a) (hprod : CountableProductTheorem)
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite) :
    DenseContinuousLocal a := by
  intro F hF ε hε
  let Ψ := positiveLinksHomeomorph (a := a) ha
  obtain ⟨J', hJ, F', hF', hread, hnorm⟩ := (hprod.1 (positiveLinkSet a)
    ((isAtMostCountable_iff_countable _).mpr inferInstance)).2.2.2 (F ∘ Ψ.symm)
      (hF.comp Ψ.symm.continuous) ε hε
  have hc : Continuous (F' ∘ Ψ) := hF'.comp Ψ.continuous
  have hobs := isBoundedObservable_of_continuous ha hc
  let 𝓜 : Set (Link a) := Subtype.val '' J'
  have hM : 𝓜.Finite := hJ.image _
  have hB : 𝓜 ⊆ positiveLinkSet a := by
    rintro _ ⟨j, -, rfl⟩
    exact j.2
  refine ⟨F' ∘ Ψ, ⟨hc, hobs, isLocalObservable_of_restrict_invariant ha hprod hfin hM hB hobs
    fun U U' e => ?_⟩, ?_⟩
  · refine hread _ _ (funext fun j => ?_)
    exact congrFun e ⟨j.1.1, j.1, j.2, rfl⟩
  · have hbdd : BddAbove (range fun g => ‖(F ∘ Ψ.symm - F') g‖) :=
      (isCompact_range ((hF.comp Ψ.symm.continuous).sub hF').norm).bddAbove
    have : Nonempty (GaugeField a) := ⟨trivialField a⟩
    refine ciSup_le fun U => le_trans ?_ hnorm
    have e : (F - F' ∘ Ψ) U = (F ∘ Ψ.symm - F') (Ψ U) := by
      simp [Pi.sub_apply]
    rw [e]
    exact le_ciSup hbdd (Ψ U)
theorem main_holds (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hlat : LatticeGeometry.LatticeGeometryStatement)
    (hprod : CountableProductTheorem) : Main := by
  intro a ha
  obtain ⟨-, hb, hc, -⟩ := hlat a ha
  have hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S → (positiveLinksWithin a S).Finite :=
    fun S hS => (hb.1 S hS).2
  have hends := hc.2.2.2.2.1
  have hsix := hc.2.2.2.2.2.2
  exact ⟨homeomorphPositiveLinks_holds ha hprod, borelEqLinkSigma_holds ha hprod,
    faceEnergyAndBoltzmannWeight_holds ha hlog hprod hfin hends hsix,
    measurableOnLinks_holds ha hprod, overwriteLinksProperties_holds, linkSigmaAndLocality_holds hfin,
    denseContinuousLocal_holds ha hprod hfin⟩
end YangMills.Construction.InfiniteLattice.ConfigurationSpace
