import YangMills.Construction.InfiniteLattice.DilationToTheUnitLatticeAsABijection
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsAndTheDilation
import YangMills.Construction.InfiniteLattice.FunctionsOfSomeOfTheBondsAndClassesStableUnderBoundedLimits
import YangMills.Construction.InfiniteLattice.OperatorsOfTheWilsonSpecification
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsProperty
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.FieldsAtSpacing
namespace GibbsEquations
variable {a : ℝ}
section Glue
variable (W : LinkWindow a) (ha : 0 < a)
theorem glue_of_mem (V : W.Assignments) (ξ : GaugeField a) {ℓ : Link a} (h : ℓ ∈ W.links) :
    W.glue ha V ξ ℓ = V ⟨ℓ, h⟩ :=
  dif_pos h
theorem glue_of_notMem (V : W.Assignments) (ξ : GaugeField a) {ℓ : Link a} (h : ℓ ∉ W.links)
    (h' : ℓ.opposite ∉ W.links) : W.glue ha V ξ ℓ = ξ ℓ :=
  (dif_neg h).trans (dif_neg h')
theorem glue_of_isPositive (V : W.Assignments) (ξ : GaugeField a) {ℓ : Link a}
    (hℓ : ℓ ∈ positiveLinkSet a) (h : ℓ ∉ W.links) : W.glue ha V ξ ℓ = ξ ℓ :=
  glue_of_notMem W ha V ξ h fun h' =>
    Link.opposite_not_isPositivelyOriented ha (mem_positiveLinks_iff.1 hℓ) (W.isPositive _ h')
theorem gaugeField_ext {U U' : GaugeField a}
    (h : ∀ ℓ ∈ positiveLinkSet a, U ℓ = U' ℓ) : U = U' := by
  refine Subtype.ext (funext fun ℓ => ?_)
  rcases mem_positiveLinks_or_opposite_mem ℓ with hℓ | hℓ
  · exact h ℓ hℓ
  · have h₁ := U.2 ℓ.opposite
    have h₂ := U'.2 ℓ.opposite
    rw [Link.opposite_opposite] at h₁ h₂
    rw [h₁, h₂, h _ hℓ]
theorem isInsensitive_iff_dependsOnlyOnLinks (H : GaugeField a → ℂ) :
    W.IsInsensitive ha H ↔
      FieldsAtSpacing.DependsOnlyOnLinks (positiveLinkSet a \ (W.links : Set (Link a))) H := by
  constructor
  · intro h U U' hU
    have hV : W.glue ha (W.restrictInside U') U = U' := gaugeField_ext fun ℓ hℓ => by
      by_cases hW : ℓ ∈ W.links
      · rw [glue_of_mem W ha _ _ hW]
        rfl
      · rw [glue_of_isPositive W ha _ _ hℓ hW]
        exact hU ℓ ⟨hℓ, hW⟩
    rw [← hV, h]
  · intro h V U
    exact h _ _ fun ℓ hℓ => glue_of_isPositive W ha V U hℓ.1 hℓ.2
theorem positiveLinks_diff_links_eq :
    positiveLinkSet a \ (W.links : Set (Link a)) =
      {ℓ | ℓ.IsPositivelyOriented ∧ ℓ ∉ W.links} := by
  ext ℓ
  simp [mem_positiveLinks_iff]
end Glue
section Insensitivity
variable (hL : LinkFunctionsStatement) (ha : 0 < a) (W : LinkWindow a)
include hL
theorem isInsensitive_iff_isBlindTo {H : GaugeField a → ℂ} (hH : IsBoundedObservable H) :
    W.IsInsensitive ha H ↔ IsBlindTo (W.links : Set (Link a)) H := by
  have h := ((hL a ha (positiveLinkSet a \ (W.links : Set (Link a)))
    Set.sdiff_subset).2.1 H hH).1
  rw [isInsensitive_iff_dependsOnlyOnLinks W ha H]
  exact (h.out 0 1).symm
theorem isInsensitive_iff_measurable {H : GaugeField a → ℂ} (hH : IsBoundedObservable H) :
    W.IsInsensitive ha H ↔ Measurable[W.exteriorSigma] H := by
  rw [isInsensitive_iff_isBlindTo hL ha W hH, IsBlindTo, positiveLinks_diff_links_eq]
theorem isInsensitive_of_mem_regionObservables {Q : Set AmbientSpace}
    (hQ : ∀ ℓ ∈ W.links, ¬ ((ℓ.initial : AmbientSpace) ∈ Q ∧ (ℓ.terminal : AmbientSpace) ∈ Q))
    {H : GaugeField a → ℂ} (hH : H ∈ regionObservables a Q) : W.IsInsensitive ha H := by
  have hc := (hL a ha ∅ (Set.empty_subset _)).2.2.1.1 Q
  have hm : H ∈ boundedRegionObservables a Q := hH
  rw [hc.2.1] at hm
  intro V U
  refine hm.2.2.1 _ _ fun ℓ hℓ => glue_of_isPositive W ha V U hℓ.1 fun hW => ?_
  exact hQ ℓ hW hℓ.2
end Insensitivity
theorem isBoundedObservable_one : IsBoundedObservable (1 : GaugeField a → ℂ) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem supNorm_le {F : GaugeField a → ℂ} {C : ℝ} (h : ∀ U, ‖F U‖ ≤ C) :
    observableSupNorm F ≤ C := by
  have : Nonempty (GaugeField a) := ⟨trivialField a⟩
  exact ciSup_le h
theorem conditionalAverageProperties (hL : LinkFunctionsStatement)
    (hK : YangMills.Construction.InfiniteLattice.ConditionalAverageProperties.claim)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (W : LinkWindow a) : GibbsEquations.ConditionalAverageProperties ha β W := by
  refine ⟨fun F hF => ?_, fun F H hF hH => ?_, fun z F hF => ?_, ?_, ?_, ?_, fun H hH =>
    isInsensitive_iff_measurable hL ha W hH, fun Q hQ H hH =>
    isInsensitive_of_mem_regionObservables hL ha W hQ hH⟩
  · obtain ⟨-, hb, hc, -⟩ := hK a ha β hβ W F F hF hF
    exact ⟨hb.1, (isInsensitive_iff_isBlindTo hL ha W hb.1).2 hb.2, hc⟩
  · exact (hK a ha β hβ W F H hF hH).2.2.2.2.2.1
  · exact (hK a ha β hβ W F F hF hF).2.2.2.2.2.2.1 z
  · exact (hK a ha β hβ W 1 1 isBoundedObservable_one isBoundedObservable_one).2.2.2.2.2.2.2.1
  · intro Fs F hFs ⟨C, hC⟩ hlim
    have hF : IsBoundedObservable F := by
      refine ⟨measurable_of_tendsto_metrizable (fun n => (hFs n).1)
        (tendsto_pi_nhds.2 hlim), C, fun U => ?_⟩
      exact le_of_tendsto (hlim U).norm (Eventually.of_forall fun n => hC n U)
    have hB : BddAbove (Set.range fun n => observableSupNorm (Fs n)) :=
      ⟨C, by rintro _ ⟨n, rfl⟩; exact supNorm_le (hC n)⟩
    exact (hK a ha β hβ W F F hF hF).2.2.2.2.2.2.2.2 Fs hFs hB hlim
  · intro H F hH hF hins
    exact (hK a ha β hβ W F H hF hH).2.2.2.1
      ((isInsensitive_iff_isBlindTo hL ha W hH).1 hins)
section Rescaling
variable (ha : 0 < a)
theorem pointRescale_eq (x : LatticePoint a) : pointRescale ha x = pointToUnit ha x := rfl
theorem pointToUnit_pointOfUnit (x : LatticePoint 1) :
    pointToUnit ha (pointOfUnit a x) = x := by apply _root_.YangMills.Construction.InfiniteLattice.pointToUnit_pointOfUnit <;> assumption
theorem pointOfUnit_pointToUnit (x : LatticePoint a) :
    pointOfUnit a (pointToUnit ha x) = x :=
  Subtype.ext (smul_inv_smul₀ ha.ne' (x : AmbientSpace))
theorem pointToUnit_add (x y : LatticePoint a) :
    pointToUnit ha (x + y) = pointToUnit ha x + pointToUnit ha y :=
  (pointToUnit ha).map_add' x y
theorem pointToUnit_injective : Function.Injective (pointToUnit ha) :=
  Function.LeftInverse.injective (pointOfUnit_pointToUnit ha)
theorem linkToUnit_injective : Function.Injective (linkToUnit ha) := by
  intro ℓ ℓ' h
  exact Link.ext (pointToUnit_injective ha (congrArg Link.initial h))
    (pointToUnit_injective ha (congrArg Link.terminal h))
theorem linkToUnit_forwardFrom (x : LatticePoint a) (μ : Fin 4) :
    linkToUnit ha (Link.forwardFrom x μ) = Link.forwardFrom (pointToUnit ha x) μ :=
  Link.ext rfl (by
    change pointToUnit ha (x + axisStep a μ) = pointToUnit ha x + axisStep 1 μ
    rw [pointToUnit_add, pointToUnit_axisStep])
theorem linkToUnit_mem_positiveLinks {ℓ : Link a} (hℓ : ℓ ∈ positiveLinkSet a) :
    linkToUnit ha ℓ ∈ positiveLinkSet 1 := by
  obtain ⟨x, κ, rfl⟩ := hℓ
  exact ⟨_, κ, linkToUnit_forwardFrom ha x κ⟩
theorem edges_rescaledPlaquette (p : ElementaryPlaquette a) :
    (rescaledPlaquette ha p).edges = p.edges.map (linkToUnit ha) := by
  simp only [ElementaryPlaquette.edges, List.map_cons, List.map_nil, linkToUnit_forwardFrom,
    pointToUnit_add, pointToUnit_axisStep, rescaledPlaquette_eq, pointRescale_eq]
theorem faceEnergy_gaugeFieldUnrescale (p : ElementaryPlaquette a) (U' : GaugeField 1) :
    faceEnergy (gaugeFieldUnrescale ha U') p = faceEnergy U' (rescaledPlaquette ha p) := by
  have h : ∀ (x : LatticePoint a) (μ : Fin 4),
      gaugeFieldUnrescale ha U' (Link.forwardFrom x μ) =
        U' (Link.forwardFrom (pointToUnit ha x) μ) := fun x μ =>
    congrArg U'.1 (linkToUnit_forwardFrom ha x μ)
  simp only [faceEnergy, faceHolonomy, h, pointToUnit_add, pointToUnit_axisStep,
    rescaledPlaquette_eq, pointRescale_eq]
theorem rescaledPlaquette_injective : Function.Injective (rescaledPlaquette ha) := by
  intro p p' h
  have h₁ : rescaledPlaquette ha p = _ := rescaledPlaquette_eq ha p
  have h₂ : rescaledPlaquette ha p' = _ := rescaledPlaquette_eq ha p'
  rw [h₁, h₂] at h
  simp only [ElementaryPlaquette.mk.injEq] at h
  exact ElementaryPlaquette.ext (pointToUnit_injective ha h.1) h.2.1 h.2.2
theorem rescaledPlaquette_surjective : Function.Surjective (rescaledPlaquette ha) := by
  intro q
  refine ⟨⟨pointOfUnit a q.corner, q.lowAxis, q.highAxis, q.lowAxis_lt_highAxis⟩, ?_⟩
  rw [rescaledPlaquette_eq]
  exact ElementaryPlaquette.ext (pointToUnit_pointOfUnit ha q.corner) rfl rfl
theorem linkToUnit_mem_links_iff (W : LinkWindow a) {ℓ : Link a} :
    linkToUnit ha ℓ ∈ (W.rescaleToUnit ha).links ↔ ℓ ∈ W.links := by
  classical
  simp only [LinkWindow.rescaleToUnit, Finset.mem_image]
  constructor
  · rintro ⟨ℓ', hℓ', h⟩
    exact linkToUnit_injective ha h ▸ hℓ'
  · exact fun h => ⟨ℓ, h, rfl⟩
theorem mem_faces_iff_rescaled (W : LinkWindow a) (p : ElementaryPlaquette a) :
    p ∈ W.faces ↔ rescaledPlaquette ha p ∈ (W.rescaleToUnit ha).faces := by
  simp only [LinkWindow.faces, facesTouching, Set.mem_ofPred_eq, edges_rescaledPlaquette,
    List.mem_map]
  constructor
  · rintro ⟨ℓ, hℓ, hW⟩
    exact ⟨_, ⟨ℓ, hℓ, rfl⟩, (linkToUnit_mem_links_iff ha W).2 hW⟩
  · rintro ⟨_, ⟨ℓ, hℓ, rfl⟩, hW⟩
    exact ⟨ℓ, hℓ, (linkToUnit_mem_links_iff ha W).1 hW⟩
theorem center_rescaledPlaquette (p : ElementaryPlaquette a) :
    (rescaledPlaquette ha p).center = inverseScaling ha p.center := by
  have h : ∀ μ : Fin 4, a⁻¹ • (Pi.single μ (a / 2) : AmbientSpace) = Pi.single μ (1 / 2) :=
    fun μ => by
      rw [← Pi.single_smul, smul_eq_mul]
      congr 1
      field_simp
  rw [rescaledPlaquette_eq]
  simp only [ElementaryPlaquette.center]
  change a⁻¹ • (p.corner : AmbientSpace) + Pi.single p.lowAxis (1 / 2) +
      Pi.single p.highAxis (1 / 2) =
    a⁻¹ • ((p.corner : AmbientSpace) + Pi.single p.lowAxis (a / 2) +
      Pi.single p.highAxis (a / 2))
  rw [smul_add, smul_add, h, h]
theorem image_cornerSet (p : ElementaryPlaquette a) :
    pointToUnit ha '' p.cornerSet = (rescaledPlaquette ha p).cornerSet := by
  rw [rescaledPlaquette_eq]
  simp only [ElementaryPlaquette.cornerSet, Set.image_insert_eq, Set.image_singleton, pointToUnit_add,
    pointToUnit_axisStep, pointRescale_eq]
theorem facesUnderRescaling (hL : LinkFunctionsStatement) (W : LinkWindow a) :
    FacesUnderRescaling ha W := by
  have facts := (hL a ha ∅ (Set.empty_subset _)).2.2.2.2.2.1
  refine ⟨fun p => ⟨?_, (facts p).2.1, image_cornerSet ha p,
    center_rescaledPlaquette ha p, ?_, mem_faces_iff_rescaled ha W p⟩, fun q => ?_⟩
  · have h : Continuous (faceFunction p) := (facts p).1.1
    refine (Complex.continuous_re.comp h).congr fun U => ?_
    simp [faceFunction]
  · exact funext fun U' => faceEnergy_gaugeFieldUnrescale ha p U'
  · obtain ⟨p, rfl⟩ := rescaledPlaquette_surjective ha q
    exact ⟨p, rfl, fun p' h => rescaledPlaquette_injective ha h⟩
variable (W : LinkWindow a)
def linksEquiv : W.links ≃ (W.rescaleToUnit ha).links :=
  Equiv.ofBijective
    (fun ℓ => ⟨linkToUnit ha ℓ, (linkToUnit_mem_links_iff ha W).2 ℓ.2⟩)
    ⟨fun ℓ ℓ' h => Subtype.ext (linkToUnit_injective ha (congrArg Subtype.val h)), by
      classical
      rintro ⟨c, hc⟩
      obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨⟨ℓ, hℓ⟩, rfl⟩⟩
def assignmentsEquiv : W.Assignments ≃ᵐ (W.rescaleToUnit ha).Assignments :=
  MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary) (linksEquiv ha W)
theorem assignmentsEquiv_apply (V : W.Assignments) (ℓ : W.links) :
    assignmentsEquiv ha W V (linksEquiv ha W ℓ) = V ℓ :=
  Equiv.piCongrLeft_apply_apply (fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (linksEquiv ha W) V ℓ
theorem measurePreserving_assignmentsEquiv :
    MeasurePreserving (assignmentsEquiv ha W) W.haarProd (W.rescaleToUnit ha).haarProd :=
  ⟨(assignmentsEquiv ha W).measurable,
    Measure.infinitePi_map_piCongrLeft (μ := fun _ => Matrices.ComplexMatrix2.haarProb)
      (linksEquiv ha W)⟩
theorem gaugeFieldUnrescale_glue (V : W.Assignments) (U' : GaugeField 1) :
    gaugeFieldUnrescale ha
        ((W.rescaleToUnit ha).glue one_pos (assignmentsEquiv ha W V) U') =
      W.glue ha V (gaugeFieldUnrescale ha U') := by
  refine gaugeField_ext fun ℓ hℓ => ?_
  change (W.rescaleToUnit ha).glue one_pos (assignmentsEquiv ha W V) U' (linkToUnit ha ℓ) = _
  by_cases hW : ℓ ∈ W.links
  · rw [glue_of_mem _ one_pos _ _ ((linkToUnit_mem_links_iff ha W).2 hW),
      glue_of_mem W ha _ _ hW]
    exact assignmentsEquiv_apply ha W V ⟨ℓ, hW⟩
  · rw [glue_of_isPositive _ one_pos _ _ (linkToUnit_mem_positiveLinks ha hℓ)
      (fun h => hW ((linkToUnit_mem_links_iff ha W).1 h)), glue_of_isPositive W ha _ _ hℓ hW]
    rfl
theorem windowAction_gaugeFieldUnrescale (U' : GaugeField 1) :
    W.windowAction (gaugeFieldUnrescale ha U') = (W.rescaleToUnit ha).windowAction U' := by
  refine finsum_mem_eq_of_bijOn (rescaledPlaquette ha)
    ⟨fun p hp => (mem_faces_iff_rescaled ha W p).1 hp,
      (rescaledPlaquette_injective ha).injOn, fun q hq => ?_⟩ fun p _ =>
    faceEnergy_gaugeFieldUnrescale ha p U'
  obtain ⟨p, rfl⟩ := rescaledPlaquette_surjective ha q
  exact ⟨p, (mem_faces_iff_rescaled ha W p).2 hq, rfl⟩
theorem conditionalAverageUnderRescaling (β : ℝ) : ConditionalAverageUnderRescaling ha β W := by
  intro F _
  funext U'
  have hnum := (measurePreserving_assignmentsEquiv ha W).integral_comp'
    (f := assignmentsEquiv ha W) (g := fun V' : (W.rescaleToUnit ha).Assignments =>
      pullToUnit ha F ((W.rescaleToUnit ha).glue one_pos V' U') *
        (Real.exp (-β * (W.rescaleToUnit ha).windowAction
          ((W.rescaleToUnit ha).glue one_pos V' U')) : ℂ))
  have hden := (measurePreserving_assignmentsEquiv ha W).integral_comp'
    (f := assignmentsEquiv ha W) (g := fun V' : (W.rescaleToUnit ha).Assignments =>
      Real.exp (-β * (W.rescaleToUnit ha).windowAction
        ((W.rescaleToUnit ha).glue one_pos V' U')))
  change W.conditionalAverage ha β F (gaugeFieldUnrescale ha U') =
    (W.rescaleToUnit ha).conditionalAverage one_pos β (pullToUnit ha F) U'
  simp only [LinkWindow.conditionalAverage]
  rw [← hnum, ← hden]
  simp only [pullToUnit, Function.comp_apply, ← windowAction_gaugeFieldUnrescale ha W,
    gaugeFieldUnrescale_glue ha W]
end Rescaling
theorem gibbsEquationsAndRescaling_holds (hL : LinkFunctionsStatement)
    (hK : YangMills.Construction.InfiniteLattice.ConditionalAverageProperties.claim)
    (hG : GibbsCharacterizations) : GibbsEquationsAndRescaling := by
  intro a ha β hβ W
  exact ⟨facesUnderRescaling ha hL W, conditionalAverageProperties hL hK ha hβ W,
    fun ν => (hG a ha β hβ ν).out 0 1, conditionalAverageUnderRescaling ha W β⟩
end GibbsEquations
end YangMills.Construction.InfiniteLattice
