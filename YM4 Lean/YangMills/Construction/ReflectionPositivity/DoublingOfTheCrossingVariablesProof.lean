import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.ReflectionPositivity.ActionInTheDoubledVariablesOfALinkMirrorProof
import YangMills.Construction.ReflectionPositivity.CoordinatesDetermineAConfigurationOfALinkMirror
import Mathlib
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.DoubledTransversal
instance instSecondCountableComplexMatrix2 : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
instance instSecondCountableSpecialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  TopologicalSpace.Subtype.secondCountableTopology _
instance isProbabilityMeasure_haarPi (ι : Type) [Countable ι] :
    IsProbabilityMeasure (Matrices.ComplexMatrix2.haarPi ι) := by
  unfold Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem coe_inv_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem opposite_opposite {D : MirrorData} (e : D.Edge) : e.opposite.opposite = e :=
  PeriodicLattice.Bond.ext rfl rfl
theorem isPositivelyOriented_or_opposite {D : MirrorData} (e : D.Edge) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by
  obtain ⟨ν, h | h⟩ := e.isNeighbour
  · exact Or.inl ⟨ν, h⟩
  · refine Or.inr ⟨ν, ?_⟩
    show e.source - e.target = _
    rw [← neg_sub, h, neg_neg]
section Measures
theorem prodMeasurableMul {X Y : Type*} [Mul X] [Mul Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableMul X] [MeasurableMul Y] : MeasurableMul (X × Y) :=
  ⟨fun c => ((measurable_const_mul c.1).comp measurable_fst).prodMk
      ((measurable_const_mul c.2).comp measurable_snd),
    fun c => ((measurable_mul_const c.1).comp measurable_fst).prodMk
      ((measurable_mul_const c.2).comp measurable_snd)⟩
theorem map_invMul_prod {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
    [MeasurableInv H] (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    Measure.map (fun p : H × H => p.2⁻¹ * p.1) (ν.prod ν) = ν := by
  have hm : Measurable fun p : H × H => p.2⁻¹ * p.1 :=
    (measurable_snd.inv).mul measurable_fst
  ext A hA
  rw [Measure.map_apply hm hA, Measure.prod_apply_symm (hm hA)]
  have h : ∀ y : H, ν ((fun x => (x, y)) ⁻¹' ((fun p : H × H => p.2⁻¹ * p.1) ⁻¹' A)) = ν A := by
    intro y
    exact measure_preimage_mul ν y⁻¹ A
  simp only [h, lintegral_const, measure_univ, mul_one]
theorem map_interleave {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (a : Measure α) (c : Measure β) [SFinite a] [SFinite c] :
    Measure.map (fun x : α × α × β × β => ((x.1, x.2.2.1), (x.2.1, x.2.2.2)))
      (a.prod (a.prod (c.prod c))) = (a.prod c).prod (a.prod c) := by
  have h1 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := α) (β := β) (γ := β)).symm)
      (a.prod (a.prod (c.prod c))) (a.prod ((a.prod c).prod c)) :=
    (MeasurePreserving.id a).prod (measurePreserving_prodAssoc a c c).symm
  have h2 : MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
      (a.prod ((a.prod c).prod c)) (a.prod ((c.prod a).prod c)) :=
    (MeasurePreserving.id a).prod (Measure.measurePreserving_swap.prod (MeasurePreserving.id c))
  have h3 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := α) (γ := β)))
      (a.prod ((c.prod a).prod c)) (a.prod (c.prod (a.prod c))) :=
    (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c a c)
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := β) (γ := α × β)).symm
      (a.prod (c.prod (a.prod c))) ((a.prod c).prod (a.prod c)) :=
    (measurePreserving_prodAssoc a c (a.prod c)).symm
  exact (h4.comp (h3.comp (h2.comp h1))).map_eq
end Measures
section Product
variable {D : MirrorData}
def positiveEdgeHomeomorph (hA : D.FieldSpaceIsProduct) :
    D.FieldSpace ≃ₜ (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) :=
  (Equiv.ofBijective _ hA.2.2.2.1).toHomeomorphOfIsInducing ⟨hA.2.2.2.2.2.2.1.symm⟩
theorem compactSpace_fieldSpace (hA : D.FieldSpaceIsProduct) :
    CompactSpace D.FieldSpace :=
  (positiveEdgeHomeomorph hA).symm.compactSpace
theorem fieldHaar_eq_map (hA : D.FieldSpaceIsProduct) :
    D.fieldHaar =
      Measure.map (positiveEdgeHomeomorph hA).symm (Matrices.ComplexMatrix2.haarPi D.PositiveEdge) := by
  have := compactSpace_fieldSpace hA
  have hc : IsCompact (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :=
    isCompact_iff_compactSpace.2 ‹_›
  have hemb : MeasurableEmbedding
      (Subtype.val : D.FieldSpace → (D.Edge → Matrices.ComplexMatrix2)) :=
    MeasurableEmbedding.subtype_coe hc.isClosed.measurableSet
  have hval : (PeriodicLattice.gaugeFieldOfPositive :
      (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) → (D.Edge → Matrices.ComplexMatrix2)) =
      Subtype.val ∘ (positiveEdgeHomeomorph hA).symm := by
    funext g
    obtain ⟨U, rfl⟩ := (positiveEdgeHomeomorph hA).surjective g
    have h := hA.2.2.2.2.2.2.2.2.1 U
    change PeriodicLattice.gaugeFieldOfPositive (positiveEdgeHomeomorph hA U) =
      ((positiveEdgeHomeomorph hA).symm (positiveEdgeHomeomorph hA U)).1
    rw [Homeomorph.symm_apply_apply]
    exact h
  unfold MirrorData.fieldHaar PeriodicLattice.productHaarMeasure PeriodicLattice.gaugeFieldHaar
  rw [hval, ← Measure.map_map hemb.measurable (positiveEdgeHomeomorph hA).symm.continuous.measurable,
    hemb.comap_map]
end Product
section Coordinates
variable {D : MirrorData} (C : LinkLevel D)
def transversalSign (e : D.PositiveEdge) : ℤˣ :=
  open Classical in
  if e.1 ∈ C.transversalEdges ∧ C.orientedAcross e.1 ≠ e.1 then -1 else 1
abbrev CoordTriple : Type :=
  (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary)
def coordTripleHaar : Measure (CoordTriple C) :=
  (C.halfHaar .pos).prod ((C.halfHaar .neg).prod C.transversalHaar)
def splitHom : (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) →* CoordTriple C where
  toFun g := (fun e => g ⟨e.1, e.2.1⟩, fun e => g ⟨e.1, e.2.1⟩, fun e => g ⟨e.1, e.2.1⟩)
  map_one' := rfl
  map_mul' _ _ := rfl
theorem continuous_splitHom : Continuous (splitHom C) := by
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_) <;>
    exact continuous_pi fun e => continuous_apply _
abbrev signedInv :
    (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) →
      (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) :=
  relabelInvert (Equiv.refl _) (transversalSign C)
theorem transversalSign_half (σ : SlabSide) (e : C.halfEdges σ) :
    transversalSign C ⟨e.1, e.2.1⟩ = 1 := by
  refine if_neg fun h => ?_
  cases σ
  · exact h.1.2.1 e.2
  · exact h.1.2.2 e.2
theorem splitCoords_eq (U : D.FieldSpace) :
    C.splitCoords U = splitHom C (signedInv C (D.positiveEdgeValues U)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext e
    change D.linkValues _ U e = (D.positiveEdgeValues U ⟨e.1, e.2.1⟩) ^
      ((transversalSign C ⟨e.1, e.2.1⟩ : ℤˣ) : ℤ)
    rw [transversalSign_half C .pos e]
    simp [MirrorData.linkValues, MirrorData.positiveEdgeValues, MirrorData.linkVar]
  · funext e
    change D.linkValues _ U e = (D.positiveEdgeValues U ⟨e.1, e.2.1⟩) ^
      ((transversalSign C ⟨e.1, e.2.1⟩ : ℤˣ) : ℤ)
    rw [transversalSign_half C .neg e]
    simp [MirrorData.linkValues, MirrorData.positiveEdgeValues, MirrorData.linkVar]
  · funext e
    change C.transversalCoords U e = (D.positiveEdgeValues U ⟨e.1, e.2.1⟩) ^
      ((transversalSign C ⟨e.1, e.2.1⟩ : ℤˣ) : ℤ)
    by_cases h : C.orientedAcross e.1 = e.1
    · have hs : transversalSign C ⟨e.1, e.2.1⟩ = 1 := if_neg fun hh => hh.2 h
      rw [hs]
      apply Subtype.ext
      change U.1 (C.orientedAcross e.1) = _
      rw [h]
      simp [MirrorData.positiveEdgeValues, MirrorData.linkVar]
    · have hs : transversalSign C ⟨e.1, e.2.1⟩ = -1 := if_pos ⟨e.2, h⟩
      rw [hs]
      apply Subtype.ext
      change U.1 (C.orientedAcross e.1) = _
      rw [(C.orientedAcross_eq_or e.1).resolve_left h, U.2.2 e.1 (mem_univ _)]
      simp only [Units.val_neg, Units.val_one, Int.reduceNeg, zpow_neg, zpow_one]
      rw [coe_inv_specialUnitary]
      rfl
theorem splitCoords_bijective
    (hK : LinkCoordinates.CoordinatesDetermineField) :
    Function.Bijective C.splitCoords := by
  have key : ∀ U : D.FieldSpace,
      C.HasCoords U (C.splitCoords U).1 (C.splitCoords U).2.1 (C.splitCoords U).2.2 :=
    fun _ => ⟨rfl, rfl, rfl⟩
  refine ⟨fun U U' h => ?_, fun t => ?_⟩
  · have h' : C.HasCoords U' (C.splitCoords U).1 (C.splitCoords U).2.1
        (C.splitCoords U).2.2 := by
      rw [h]
      exact key U'
    exact ((hK D C).1 _ _ _).1.unique (key U) h'
  · obtain ⟨a, b, c⟩ := t
    obtain ⟨h₁, h₂, h₃⟩ := ((hK D C).1 a b c).2
    exact ⟨C.fieldOfCoords a b c, Prod.ext h₁ (Prod.ext h₂ h₃)⟩
theorem splitCoords_fieldOfCoords
    (hK : LinkCoordinates.CoordinatesDetermineField)
    (a : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (b : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (c : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) :
    C.splitCoords (C.fieldOfCoords a b c) = (a, b, c) := by
  obtain ⟨h₁, h₂, h₃⟩ := ((hK D C).1 a b c).2
  exact Prod.ext h₁ (Prod.ext h₂ h₃)
theorem continuous_linkValues (S : Set D.Edge) : Continuous (D.linkValues S) :=
  continuous_pi fun e =>
    Continuous.subtype_mk ((continuous_apply e.1).comp continuous_subtype_val) _
theorem continuous_transversalCoords : Continuous C.transversalCoords :=
  continuous_pi fun e =>
    Continuous.subtype_mk ((continuous_apply (C.orientedAcross e.1)).comp continuous_subtype_val) _
theorem continuous_splitCoords : Continuous C.splitCoords :=
  (continuous_linkValues _).prodMk
    ((continuous_linkValues _).prodMk (continuous_transversalCoords C))
variable [Finite D.Edge]
theorem isHomeomorph_splitCoords (hA : D.FieldSpaceIsProduct)
    (hK : LinkCoordinates.CoordinatesDetermineField) : IsHomeomorph C.splitCoords := by
  have := compactSpace_fieldSpace hA
  exact (isHomeomorph_iff_continuous_bijective).2
    ⟨continuous_splitCoords C, splitCoords_bijective C hK⟩
theorem splitHom_bijective (hA : D.FieldSpaceIsProduct)
    (hK : LinkCoordinates.CoordinatesDetermineField) (hS : RelabelInvertMeasurePreserving) :
    Function.Bijective (splitHom C) := by
  have hR : Function.Bijective (signedInv C) :=
    (hS _ _ (Equiv.refl _) (transversalSign C)).1.bijective
  have hcomp : C.splitCoords ∘ (positiveEdgeHomeomorph hA).symm = splitHom C ∘ signedInv C := by
    funext g
    obtain ⟨U, rfl⟩ := (positiveEdgeHomeomorph hA).surjective g
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    exact splitCoords_eq C U
  have hB : Function.Bijective (splitHom C ∘ signedInv C) := by
    rw [← hcomp]
    exact (splitCoords_bijective C hK).comp (positiveEdgeHomeomorph hA).symm.bijective
  exact ⟨fun x y h => by
      obtain ⟨x', rfl⟩ := hR.2 x
      obtain ⟨y', rfl⟩ := hR.2 y
      exact congrArg _ (hB.1 h),
    fun t => by
      obtain ⟨x, hx⟩ := hB.2 t
      exact ⟨_, hx⟩⟩
theorem map_splitHom (hA : D.FieldSpaceIsProduct)
    (hK : LinkCoordinates.CoordinatesDetermineField) (hS : RelabelInvertMeasurePreserving)
    (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement) :
    Measure.map (splitHom C) (Matrices.ComplexMatrix2.haarPi D.PositiveEdge) = coordTripleHaar C := by
  have hbij := splitHom_bijective C hA hK hS
  have hhome : IsHomeomorph (splitHom C) :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨continuous_splitHom C, hbij⟩
  let e : (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) ≃* CoordTriple C :=
    MulEquiv.ofBijective (splitHom C) hbij
  let h : (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) ≃ₜ CoordTriple C :=
    hhome.homeomorph
  have hsymm : Measurable e.symm := by
    have : (e.symm : CoordTriple C → _) = h.symm := rfl
    rw [this]
    exact h.symm.continuous.measurable
  have hLp : (C.halfHaar .pos).IsMulLeftInvariant := (hH.2.1 _).2.2.2.1
  have hLm : (C.halfHaar .neg).IsMulLeftInvariant := (hH.2.1 _).2.2.2.1
  have hLc : C.transversalHaar.IsMulLeftInvariant := (hH.2.1 _).2.2.2.1
  have hPp : IsProbabilityMeasure (C.halfHaar .pos) := isProbabilityMeasure_haarPi _
  have hPm : IsProbabilityMeasure (C.halfHaar .neg) := isProbabilityMeasure_haarPi _
  have hPc : IsProbabilityMeasure C.transversalHaar := isProbabilityMeasure_haarPi _
  have hM : MeasurableMul ((C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary) ×
      (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary)) :=
    prodMeasurableMul
  have hTL0 : ((C.halfHaar .neg).prod C.transversalHaar).IsMulLeftInvariant := inferInstance
  have hTL : (coordTripleHaar C).IsMulLeftInvariant := by
    unfold coordTripleHaar
    exact Measure.prod.instIsMulLeftInvariant
  have hTP : IsProbabilityMeasure (coordTripleHaar C) := by
    unfold coordTripleHaar
    infer_instance
  have hP' : IsProbabilityMeasure (Measure.map e.symm (coordTripleHaar C)) :=
    Measure.isProbabilityMeasure_map hsymm.aemeasurable
  have hL' : (Measure.map e.symm (coordTripleHaar C)).IsMulLeftInvariant :=
    isMulLeftInvariant_map e.symm.toMulHom hsymm e.symm.surjective
  have hu := (hH.2.1 D.PositiveEdge).2.1
  have heq : Matrices.ComplexMatrix2.haarPi D.PositiveEdge = Measure.map e.symm (coordTripleHaar C) :=
    hu.unique ⟨(hH.2.1 _).2.2.1, (hH.2.1 _).2.2.2.1⟩ ⟨hP', hL'⟩
  rw [heq, Measure.map_map (continuous_splitHom C).measurable hsymm]
  have hid : (splitHom C) ∘ e.symm = id := by
    funext t
    exact e.apply_symm_apply t
  rw [hid, Measure.map_id]
theorem map_splitCoords (hA : D.FieldSpaceIsProduct)
    (hK : LinkCoordinates.CoordinatesDetermineField) (hS : RelabelInvertMeasurePreserving)
    (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement) :
    Measure.map C.splitCoords D.fieldHaar = coordTripleHaar C := by
  have hR := hS _ _ (Equiv.refl D.PositiveEdge) (transversalSign C)
  have hRm : Measurable (signedInv C) := hR.1.continuous.measurable
  have hcomp : C.splitCoords ∘ (positiveEdgeHomeomorph hA).symm = splitHom C ∘ signedInv C := by
    funext g
    obtain ⟨U, rfl⟩ := (positiveEdgeHomeomorph hA).surjective g
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    exact splitCoords_eq C U
  rw [fieldHaar_eq_map hA,
    Measure.map_map (continuous_splitCoords C).measurable
      (positiveEdgeHomeomorph hA).symm.continuous.measurable, hcomp,
    ← Measure.map_map (continuous_splitHom C).measurable hRm, hR.2.1]
  exact map_splitHom C hA hK hS hH
end Coordinates
section Sorted
variable {D : MirrorData} (C : LinkLevel D)
theorem positiveEdgesPartition (hV : Disjoint (C.halfVertices .pos) (C.halfVertices .neg)) :
    PositiveEdgesPartition C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext e
    constructor
    · intro he
      by_cases h₁ : e ∈ C.halfEdges .pos
      · exact Or.inl (Or.inl h₁)
      · by_cases h₂ : e ∈ C.halfEdges .neg
        · exact Or.inl (Or.inr h₂)
        · exact Or.inr ⟨he, h₁, h₂⟩
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1
  · refine Set.disjoint_left.2 fun e h₁ h₂ => ?_
    exact Set.disjoint_left.1 hV h₁.2.1 h₂.2.1
  · exact Set.disjoint_left.2 fun e h₁ h₂ => h₂.2.1 h₁
  · exact Set.disjoint_left.2 fun e h₁ h₂ => h₂.2.2 h₁
end Sorted
section Algebras
variable {D : MirrorData} (C : LinkLevel D)
theorem borel_pi_eq (S : Set D.Edge) :
    borel (S → Matrices.ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
  BorelSpace.measurable_eq.symm
theorem borel_fieldSpace_eq :
    borel D.FieldSpace = (inferInstance : MeasurableSpace D.FieldSpace) :=
  (BorelSpace.measurable_eq (α := D.FieldSpace)).symm
theorem mem_halfAlgebra_iff (σ : SlabSide) (F : D.FieldSpace → ℂ) :
    F ∈ C.halfAlgebra σ ↔ ∃ Φ : (C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary) → ℂ,
      Measurable Φ ∧ TestFunctions.IsBoundedFun Φ ∧ ∀ U, F U = Φ (C.halfCoords σ U) := by
  constructor
  · rintro ⟨Φ, hm, hb, rfl⟩
    rw [borel_pi_eq] at hm
    exact ⟨Φ, hm, hb, fun _ => rfl⟩
  · rintro ⟨Φ, hm, hb, h⟩
    refine ⟨Φ, ?_, hb, funext h⟩
    rw [borel_pi_eq]
    exact hm
theorem halfFunction_eq {σ : SlabSide} (hs : Function.Surjective (C.halfCoords σ))
    {F : D.FieldSpace → ℂ} {Φ : (C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (h : ∀ U, F U = Φ (C.halfCoords σ U)) : C.halfFunction σ F = Φ := by
  have hspec : ∀ U, F U = C.halfFunction σ F (C.halfCoords σ U) :=
    Classical.epsilon_spec (p := fun Ψ : (C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary) → ℂ =>
      ∀ U, F U = Ψ (C.halfCoords σ U)) ⟨Φ, h⟩
  funext u
  obtain ⟨U, rfl⟩ := hs u
  rw [← hspec, h]
theorem extendByOne_of_mem {S : Set D.Edge} (g : S → Matrices.ComplexMatrix2.specialUnitary)
    {e : D.Edge} (h : e ∈ S) : LinkLevel.extendByOne g e = g ⟨e, h⟩ :=
  dif_pos h
theorem continuous_extendByOne {S : Set D.Edge} (e : D.Edge) :
    Continuous fun g : S → Matrices.ComplexMatrix2.specialUnitary => LinkLevel.extendByOne g e := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.DoubledAction.continuous_extendByOne <;> assumption
def slabLinkValues (σ : SlabSide) (u : C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary) :
    C.edgesInSlab σ → Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  fun e => if e.1.IsPositivelyOriented then LinkLevel.extendByOne u e.1
    else (LinkLevel.extendByOne u e.1.opposite)⁻¹
theorem continuous_slabLinkValues (σ : SlabSide) : Continuous (slabLinkValues C σ) := by
  refine continuous_pi fun e => ?_
  by_cases h : e.1.IsPositivelyOriented
  · simp only [slabLinkValues, if_pos h]
    exact continuous_extendByOne _
  · simp only [slabLinkValues, if_neg h]
    exact (continuous_extendByOne _).inv
theorem halfEdges_subset_edgesInSlab (σ : SlabSide) : C.halfEdges σ ⊆ C.edgesInSlab σ :=
  fun _ he => ⟨he.2.1.2, he.2.2.2⟩
theorem mem_halfEdges_of_mem_slab {σ : SlabSide} {e : D.Edge} (he : e ∈ C.edgesInSlab σ)
    (hp : e.IsPositivelyOriented) : e ∈ C.halfEdges σ :=
  ⟨hp, ⟨e.source.2, he.1⟩, ⟨e.target.2, he.2⟩⟩
theorem linkValues_edgesInSlab (σ : SlabSide) (U : D.FieldSpace) :
    D.linkValues (C.edgesInSlab σ) U = slabLinkValues C σ (C.halfCoords σ U) := by
  funext e
  by_cases h : e.1.IsPositivelyOriented
  · have hm := mem_halfEdges_of_mem_slab C e.2 h
    simp only [slabLinkValues, if_pos h, extendByOne_of_mem _ hm]
    rfl
  · have hr : e.1.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite e.1).resolve_left h
    have hm : e.1.opposite ∈ C.halfEdges σ :=
      mem_halfEdges_of_mem_slab C (e := e.1.opposite) ⟨e.2.2, e.2.1⟩ hr
    simp only [slabLinkValues, if_neg h, extendByOne_of_mem _ hm]
    apply Subtype.ext
    rw [coe_inv_specialUnitary]
    change U.1 e.1 = (U.1 e.1.opposite)⁻¹
    have := U.2.2 e.1.opposite (mem_univ _)
    rw [opposite_opposite] at this
    exact this
theorem isBoundedMeasurableInLinks_iff (σ : SlabSide) (F : D.FieldSpace → ℂ) :
    D.IsBoundedMeasurableInLinks (C.edgesInSlab σ) F ↔ F ∈ C.halfAlgebra σ := by
  rw [mem_halfAlgebra_iff]
  constructor
  · rintro ⟨Φ, hm, hb, rfl⟩
    rw [borel_pi_eq] at hm
    refine ⟨Φ ∘ slabLinkValues C σ, hm.comp (continuous_slabLinkValues C σ).measurable, ?_,
      fun U => ?_⟩
    · obtain ⟨K, hK⟩ := hb
      exact ⟨K, fun u => hK _⟩
    · simp only [Function.comp_apply, linkValues_edgesInSlab]
  · rintro ⟨Φ, hm, hb, h⟩
    have hi : Continuous fun g : C.edgesInSlab σ → Matrices.ComplexMatrix2.specialUnitary =>
        g ∘ Set.inclusion (halfEdges_subset_edgesInSlab C σ) :=
      continuous_pi fun e => continuous_apply _
    refine ⟨Φ ∘ fun g => g ∘ Set.inclusion (halfEdges_subset_edgesInSlab C σ), ?_, ?_, ?_⟩
    · rw [borel_pi_eq]
      exact hm.comp hi.measurable
    · obtain ⟨K, hK⟩ := hb
      exact ⟨K, fun u => hK _⟩
    · funext U
      rw [h]
      rfl
theorem halfAlgebraEqSlabFunctions (σ : SlabSide) (hs : Function.Surjective (C.halfCoords σ)) :
    HalfAlgebraEqSlabFunctions C σ := by
  refine ⟨isBoundedMeasurableInLinks_iff C σ, fun F hF => ?_⟩
  obtain ⟨Φ, hm, hb, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
  rw [halfFunction_eq C hs h, borel_pi_eq]
  exact ⟨hb, hm⟩
theorem measurable_halfCoords (σ : SlabSide) : Measurable (C.halfCoords σ) :=
  (continuous_linkValues _).measurable
theorem halfAlgebraClosed (σ : SlabSide) : HalfAlgebraClosed C σ := by
  refine ⟨fun F hF => ?_, fun z => ?_, fun F hF F' hF' => ?_, fun z F hF => ?_,
    fun F hF F' hF' => ?_, fun F hF => ?_⟩
  · obtain ⟨Φ, hm, ⟨K, hK⟩, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
    refine ⟨⟨K, fun U => ?_⟩, ?_⟩
    · rw [h]
      exact hK _
    · rw [borel_fieldSpace_eq, funext h]
      exact hm.comp (measurable_halfCoords C σ)
  · exact (mem_halfAlgebra_iff C σ _).2
      ⟨fun _ => z, measurable_const, ⟨‖z‖, fun _ => le_rfl⟩, fun _ => rfl⟩
  · obtain ⟨Φ, hm, ⟨K, hK⟩, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
    obtain ⟨Φ', hm', ⟨K', hK'⟩, h'⟩ := (mem_halfAlgebra_iff C σ F').1 hF'
    refine (mem_halfAlgebra_iff C σ _).2 ⟨Φ + Φ', hm.add hm',
      ⟨K + K', fun v => (norm_add_le _ _).trans (add_le_add (hK v) (hK' v))⟩, fun U => ?_⟩
    simp only [Pi.add_apply, h, h']
  · obtain ⟨Φ, hm, ⟨K, hK⟩, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
    refine (mem_halfAlgebra_iff C σ _).2 ⟨z • Φ, hm.const_smul z,
      ⟨‖z‖ * K, fun v => ?_⟩, fun U => ?_⟩
    · rw [Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hK v) (norm_nonneg _)
    · simp only [Pi.smul_apply, h]
  · obtain ⟨Φ, hm, ⟨K, hK⟩, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
    obtain ⟨Φ', hm', ⟨K', hK'⟩, h'⟩ := (mem_halfAlgebra_iff C σ F').1 hF'
    refine (mem_halfAlgebra_iff C σ _).2 ⟨Φ * Φ', hm.mul hm',
      ⟨K * K', fun v => ?_⟩, fun U => ?_⟩
    · rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hK v) (hK' v) (norm_nonneg _) ((norm_nonneg _).trans (hK v))
    · simp only [Pi.mul_apply, h, h']
  · obtain ⟨Φ, hm, ⟨K, hK⟩, h⟩ := (mem_halfAlgebra_iff C σ F).1 hF
    refine (mem_halfAlgebra_iff C σ _).2 ⟨fun v => starRingEnd ℂ (Φ v),
      Complex.continuous_conj.measurable.comp hm, ⟨K, fun v => ?_⟩, fun U => ?_⟩
    · rw [RCLike.norm_conj]
      exact hK v
    · simp only [h]
theorem halfFunctionLinearIsometric (σ : SlabSide) (hs : Function.Surjective (C.halfCoords σ)) :
    HalfFunctionLinearIsometric C σ := by
  have hspec : ∀ F ∈ C.halfAlgebra σ, ∀ U, F U = C.halfFunction σ F (C.halfCoords σ U) :=
    fun F hF U => C.halfFunction_spec hF U
  refine ⟨fun F hF F' hF' => ?_, fun z F hF => ?_, fun F hF => ?_⟩
  · refine halfFunction_eq C hs fun U => ?_
    simp only [Pi.add_apply, ← hspec F hF, ← hspec F' hF']
  · refine halfFunction_eq C hs fun U => ?_
    simp only [Pi.smul_apply, ← hspec F hF]
  · have h : (fun U => ‖F U‖) = fun U => ‖C.halfFunction σ F (C.halfCoords σ U)‖ := by
      funext U
      rw [← hspec F hF]
    simp only [h]
    exact (hs.iSup_comp fun u => ‖C.halfFunction σ F u‖).symm
end Algebras
section Relabelling
variable {D : MirrorData} (C : LinkLevel D)
def reflectionSign (e : C.halfEdges .pos) : ℤˣ :=
  open Classical in
  if e.1.IsParallelToAxis D.dir then -1 else 1
theorem transfer_eq_relabelInvert
    (hθ : BijOn C.positiveReflectedEdge (C.halfEdges .pos) (C.halfEdges .neg)) :
    C.transfer = relabelInvert (hθ.equiv _) (reflectionSign C) := by
  funext u' e
  have hm : C.positiveReflectedEdge e.1 ∈ C.halfEdges .neg := hθ.mapsTo e.2
  have he : LinkLevel.extendByOne u' (C.positiveReflectedEdge e.1) = u' (hθ.equiv _ e) :=
    extendByOne_of_mem u' hm
  by_cases h : e.1.IsParallelToAxis D.dir
  · have hs : reflectionSign C e = -1 := if_pos h
    simp only [LinkLevel.transfer, if_pos h, relabelInvert, hs, he]
    simp
  · have hs : reflectionSign C e = 1 := if_neg h
    simp only [LinkLevel.transfer, if_neg h, relabelInvert, hs, he]
    simp
variable [Finite D.Edge]
theorem transferIsReflection (hS : RelabelInvertMeasurePreserving)
    (hθ : BijOn C.positiveReflectedEdge (C.halfEdges .pos) (C.halfEdges .neg))
    (s : D.Symmetry) (hs : s.toFun = C.refl)
    (hp : HalfSpaces.PullbackOnPositiveEdges C s) :
    TransferIsReflection C := by
  have hR := hS _ _ (hθ.equiv _) (reflectionSign C)
  have hco : ∀ U : D.FieldSpace, C.halfCoords .pos (C.reflectField U) =
      C.transfer (C.halfCoords .neg U) := by
    intro U
    funext e
    have hm : C.positiveReflectedEdge e.1 ∈ C.halfEdges .neg := hθ.mapsTo e.2
    have hval : (C.reflectField U).1 e.1 =
        MirrorData.Symmetry.pullback s U.1 e.1 := by
      rw [C.reflectField_val s hs]
    apply Subtype.ext
    change (C.reflectField U).1 e.1 = _
    rw [hval]
    by_cases h : e.1.IsParallelToAxis D.dir
    · simp only [LinkLevel.transfer, if_pos h, extendByOne_of_mem _ hm]
      rw [(hp U e.1 e.2).2 h, coe_inv_specialUnitary]
      rfl
    · simp only [LinkLevel.transfer, if_neg h, extendByOne_of_mem _ hm]
      rw [(hp U e.1 e.2).1 h]
      rfl
  refine ⟨?_, ?_, hco, fun F hF U => ?_⟩
  · rw [transfer_eq_relabelInvert C hθ]
    exact hR.1
  · rw [transfer_eq_relabelInvert C hθ]
    exact hR.2.1
  · rw [← hco]
    exact C.halfFunction_spec hF _
end Relabelling
section Doubling
variable {D : MirrorData} (C : LinkLevel D)
def quadrupleToTriple (x : C.QuadrupleSpace) : CoordTriple C :=
  (x.1, x.2.1, C.transversalQuot x.2.2.1 x.2.2.2)
theorem continuous_transversalQuot :
    Continuous fun p : (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) ×
      (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) => C.transversalQuot p.1 p.2 :=
  continuous_pi fun e =>
    ((continuous_apply e).comp continuous_snd).inv.mul ((continuous_apply e).comp continuous_fst)
theorem continuous_quadrupleToTriple : Continuous (quadrupleToTriple C) :=
  continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
    ((continuous_transversalQuot C).comp (continuous_snd.comp continuous_snd)))
variable [Finite D.Edge]
theorem map_quadrupleToTriple (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement) :
    Measure.map (quadrupleToTriple C) C.quadrupleHaar = coordTripleHaar C := by
  have hLc : C.transversalHaar.IsMulLeftInvariant := (hH.2.1 _).2.2.2.1
  have hPp : IsProbabilityMeasure (C.halfHaar .pos) := isProbabilityMeasure_haarPi _
  have hPm : IsProbabilityMeasure (C.halfHaar .neg) := isProbabilityMeasure_haarPi _
  have hPc : IsProbabilityMeasure C.transversalHaar := isProbabilityMeasure_haarPi _
  have hq : MeasurePreserving (fun p : (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) ×
      (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) => C.transversalQuot p.1 p.2)
      (C.transversalHaar.prod C.transversalHaar) C.transversalHaar :=
    ⟨(continuous_transversalQuot C).measurable, map_invMul_prod C.transversalHaar⟩
  exact ((MeasurePreserving.id (C.halfHaar .pos)).prod
    ((MeasurePreserving.id (C.halfHaar .neg)).prod hq)).map_eq
theorem integralDoubled (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hA : D.FieldSpaceIsProduct) (hK : LinkCoordinates.CoordinatesDetermineField)
    (hS : RelabelInvertMeasurePreserving) (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement) :
    IntegralDoubled C E := by
  intro Υ hb hm
  rw [borel_fieldSpace_eq] at hm
  have hhome := isHomeomorph_splitCoords C hA hK
  let h : D.FieldSpace ≃ₜ CoordTriple C := hhome.homeomorph
  have hh : ∀ U, h U = C.splitCoords U := fun _ => rfl
  have hd : C.liftToQuadruple Υ = (Υ ∘ h.symm) ∘ quadrupleToTriple C := by
    funext x
    change Υ (C.fieldOfCoords _ _ _) = Υ (h.symm _)
    congr 1
    apply h.injective
    rw [h.apply_symm_apply, hh]
    exact splitCoords_fieldOfCoords C hK _ _ _
  have hg : Measurable (Υ ∘ h.symm) := hm.comp h.symm.continuous.measurable
  have e₁ : ∫ U, Υ U ∂D.fieldHaar = ∫ t, (Υ ∘ h.symm) t ∂coordTripleHaar C := by
    rw [← map_splitCoords C hA hK hS hH,
      integral_map (continuous_splitCoords C).measurable.aemeasurable hg.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [Function.comp_apply]
    rw [← hh, h.symm_apply_apply]
  have e₂ : ∫ x, C.liftToQuadruple Υ x ∂C.quadrupleHaar =
      ∫ t, (Υ ∘ h.symm) t ∂coordTripleHaar C := by
    rw [← map_quadrupleToTriple C hH,
      integral_map (continuous_quadrupleToTriple C).measurable.aemeasurable
        hg.aestronglyMeasurable, hd]
    rfl
  refine ⟨?_, ?_, e₁.trans e₂.symm⟩
  · obtain ⟨B, hB⟩ := hb
    refine ⟨B, fun x => ?_⟩
    rw [hd]
    exact hB _
  · have hbor : borel C.QuadrupleSpace = (inferInstance : MeasurableSpace C.QuadrupleSpace) :=
      (BorelSpace.measurable_eq (α := C.QuadrupleSpace)).symm
    rw [hbor, hd]
    exact hg.comp (continuous_quadrupleToTriple C).measurable
theorem pairPointsIndependent (hR : TransferIsReflection C) :
    PairPointsIndependent C := by
  have hPp : IsProbabilityMeasure (C.halfHaar .pos) := isProbabilityMeasure_haarPi _
  have hPm : IsProbabilityMeasure (C.halfHaar .neg) := isProbabilityMeasure_haarPi _
  have hPc : IsProbabilityMeasure C.transversalHaar := isProbabilityMeasure_haarPi _
  have hιc : Continuous C.transfer := hR.1.continuous
  have hι : MeasurePreserving C.transfer (C.halfHaar .neg) (C.halfHaar .pos) :=
    ⟨hιc.measurable, hR.2.1⟩
  have hcont : Continuous C.pairPoints :=
    (continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
      ((hιc.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have hmap : Measure.map C.pairPoints C.quadrupleHaar = C.doubleHaar.prod C.doubleHaar := by
    have h₁ : MeasurePreserving (Prod.map id (Prod.map C.transfer id)) C.quadrupleHaar
        ((C.halfHaar .pos).prod ((C.halfHaar .pos).prod
          (C.transversalHaar.prod C.transversalHaar))) :=
      (MeasurePreserving.id (C.halfHaar .pos)).prod
        (hι.prod (MeasurePreserving.id (C.transversalHaar.prod C.transversalHaar)))
    have h₂ := map_interleave (C.halfHaar .pos) C.transversalHaar
    have hm₂ : Measurable fun x : (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
        (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
          (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) ×
          (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) =>
            ((x.1, x.2.2.1), (x.2.1, x.2.2.2)) :=
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    rw [← h₁.map_eq, Measure.map_map hm₂ h₁.measurable] at h₂
    exact h₂
  refine ⟨hcont, hmap, fun φ ψ _ hφ _ hψ => ?_⟩
  have hbor : borel C.DoubleSpace = (inferInstance : MeasurableSpace C.DoubleSpace) :=
    (BorelSpace.measurable_eq (α := C.DoubleSpace)).symm
  rw [hbor] at hφ hψ
  have hPd : IsProbabilityMeasure C.doubleHaar := by
    unfold LinkLevel.doubleHaar
    infer_instance
  have hg : Measurable fun z : C.DoubleSpace × C.DoubleSpace =>
      φ z.1 * starRingEnd ℂ (ψ z.2) :=
    (hφ.comp measurable_fst).mul
      (Complex.continuous_conj.measurable.comp (hψ.comp measurable_snd))
  have e := integral_map (μ := C.quadrupleHaar) hcont.measurable.aemeasurable
    hg.aestronglyMeasurable
  rw [hmap] at e
  rw [← e, integral_prod_mul φ fun ω => starRingEnd ℂ (ψ ω), integral_conj]
end Doubling
theorem doublingProperties (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hK : LinkCoordinates.CoordinatesDetermineField)
    (hG : HalfSpaces.HalfSpaceStructure)
    (hP : FieldSpaceAndFaceEnergies.Statement) : DoublingProperties := by
  intro D C
  obtain ⟨hA, hS, -⟩ := hP D
  have hfin : Finite D.Edge := hA.2.1
  obtain ⟨hsites, -, -, hθ, -, -, -, s, hs, hp, -⟩ := hG D C
  have hsurj : ∀ σ : SlabSide, Function.Surjective (C.halfCoords σ) := (hK D C).2
  have hR := transferIsReflection C hS hθ s hs hp
  exact ⟨positiveEdgesPartition C hsites.2.2.2.2.2.1,
    ⟨isHomeomorph_splitCoords C hA hK, map_splitCoords C hA hK hS hH⟩,
    fun σ => ⟨halfAlgebraEqSlabFunctions C σ (hsurj σ), halfAlgebraClosed C σ,
      halfFunctionLinearIsometric C σ (hsurj σ)⟩,
    hR, integralDoubled C ℝ hA hK hS hH,
    integralDoubled C ℂ hA hK hS hH, pairPointsIndependent C hR⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.DoubledTransversal
end
