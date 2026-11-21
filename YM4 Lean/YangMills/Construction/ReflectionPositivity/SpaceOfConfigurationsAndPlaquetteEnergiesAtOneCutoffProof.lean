import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import Mathlib
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies
open YangMills.Construction.Matrices
instance instSecondCountableComplexMatrix2 : SecondCountableTopology ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
instance instSecondCountableSpecialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary :=
  TopologicalSpace.Subtype.secondCountableTopology _
section Relabel
variable {X X' : Type}
theorem continuous_relabelInvert (σ : X' ≃ X) (s : X' → ℤˣ) :
    Continuous (relabelInvert σ s) :=
  continuous_pi fun x' => (continuous_apply (σ x')).zpow _
theorem zpow_unit_involutive (e : ℤˣ) (g : ComplexMatrix2.specialUnitary) :
    (g ^ (e : ℤ)) ^ (e : ℤ) = g := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp
def relabelInvertHomeomorph (σ : X' ≃ X) (s : X' → ℤˣ) :
    (X → ComplexMatrix2.specialUnitary) ≃ₜ (X' → ComplexMatrix2.specialUnitary) where
  toFun := relabelInvert σ s
  invFun := relabelInvert σ.symm (s ∘ σ.symm)
  left_inv g := by
    funext x
    simp [relabelInvert, zpow_unit_involutive]
  right_inv g := by
    funext x'
    simp [relabelInvert, zpow_unit_involutive]
  continuous_toFun := continuous_relabelInvert σ s
  continuous_invFun := continuous_relabelInvert σ.symm (s ∘ σ.symm)
theorem haarProb_map_zpow_unit (hH : ComplexMatrix2.HaarExpChartProperties) (e : ℤˣ) :
    Measure.map (fun g : ComplexMatrix2.specialUnitary => g ^ (e : ℤ)) ComplexMatrix2.haarProb =
      ComplexMatrix2.haarProb := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp
  · simpa using hH.2.2.2
theorem haarPi_map_relabelInvert [Finite X] [Finite X'] (hH : ComplexMatrix2.HaarExpChartProperties)
    (σ : X' ≃ X) (s : X' → ℤˣ) :
    Measure.map (relabelInvert σ s) (ComplexMatrix2.haarPi X) = ComplexMatrix2.haarPi X' := by
  classical
  have hmeas : Measurable (relabelInvert σ s) := (continuous_relabelInvert σ s).measurable
  have hzpow : ∀ e : ℤˣ, Measurable fun g : ComplexMatrix2.specialUnitary => g ^ (e : ℤ) :=
    fun e => (continuous_zpow _).measurable
  refine Measure.eq_infinitePi _ fun I S hS => ?_
  rw [Measure.map_apply hmeas (.pi I.countable_toSet fun i _ => hS i)]
  have hpre : relabelInvert σ s ⁻¹' (I : Set X').pi S =
      ((I.map σ.toEmbedding : Finset X) : Set X).pi
        (fun x => (fun g : ComplexMatrix2.specialUnitary => g ^ ((s (σ.symm x) : ℤˣ) : ℤ)) ⁻¹'
          S (σ.symm x)) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map_equiv,
      relabelInvert]
    constructor
    · intro h x hx
      simpa using h _ hx
    · intro h x' hx'
      simpa using h (σ x') (by simpa using hx')
  rw [hpre]
  unfold ComplexMatrix2.haarPi
  rw [Measure.infinitePi_pi _ (fun x _ => hzpow _ (hS _)), Finset.prod_map]
  refine Finset.prod_congr rfl fun x' _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  rw [← Measure.map_apply (hzpow _) (hS x'), haarProb_map_zpow_unit hH]
theorem relabelInvert_integral_eq (hH : ComplexMatrix2.HaarExpChartProperties)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Finite X] [Finite X'] (σ : X' ≃ X) (s : X' → ℤˣ) :
    RelabelInvertIntegralEq E σ s := by
  intro F hF
  have hbX : borel (X → ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
    BorelSpace.measurable_eq.symm
  have hbX' : borel (X' → ComplexMatrix2.specialUnitary) = MeasurableSpace.pi :=
    BorelSpace.measurable_eq.symm
  have hFm : Measurable F := by
    have h := hF.1
    rwa [hbX'] at h
  have hmeas : Measurable (relabelInvert σ s) := (continuous_relabelInvert σ s).measurable
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hbX]
    exact hFm.comp hmeas
  · obtain ⟨C, hC⟩ := hF.2
    exact ⟨C, fun x => hC _⟩
  · have h := integral_map (μ := ComplexMatrix2.haarPi X) hmeas.aemeasurable
      hFm.aestronglyMeasurable
    rw [haarPi_map_relabelInvert hH σ s] at h
    exact h.symm
theorem relabelInvert_measurePreserving (hH : ComplexMatrix2.HaarExpChartProperties) :
    RelabelInvertMeasurePreserving := by
  intro X X' _ _ σ s
  exact ⟨(relabelInvertHomeomorph σ s).isHomeomorph, haarPi_map_relabelInvert hH σ s,
    relabelInvert_integral_eq hH ℝ σ s, relabelInvert_integral_eq hH ℂ σ s⟩
end Relabel
section Edges
variable {L m : ℕ} {j : ℤ}
theorem continuous_plaquetteEnergy (p : PeriodicLattice.Plaquette L m j) :
    Continuous fun U : PeriodicLattice.Bond L m j → ComplexMatrix2 =>
      PeriodicLattice.plaquetteCost U p := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.continuous_plaquetteCost <;> assumption
theorem opposite_opposite (b : PeriodicLattice.Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem isPositivelyOriented_or_opposite (b : PeriodicLattice.Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
end Edges
namespace OfData
variable (D : MirrorData)
theorem blockingFactor_pos : 0 < D.L := by
  have := D.isAdmissible.2
  omega
theorem one_lt_blockingFactor : 1 < D.L := by
  have := D.isAdmissible.2
  omega
theorem scaleExponent_pos : 0 < ((D.m : ℕ) : ℤ) + ((D.K : ℕ) : ℤ) := by
  have h1 := D.m.pos
  have h2 := D.K.pos
  omega
theorem neg_m_le_K : -((D.m : ℕ) : ℤ) ≤ ((D.K : ℕ) : ℤ) := by
  have h1 := D.m.pos
  have h2 := D.K.pos
  omega
variable {D}
theorem latticeFacts (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Finite (PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ)) ∧
      Topology.IsEmbedding (PeriodicLattice.gaugeFieldOfPositive :
        (PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ) →
          ComplexMatrix2.specialUnitary) → _) ∧
      range (PeriodicLattice.gaugeFieldOfPositive :
        (PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ) →
          ComplexMatrix2.specialUnitary) → _) =
        PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) ∧
      IsCompact (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) ∧
      TopologicalSpace.MetrizableSpace
        (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :=
  (hC D.L D.m ((D.K : ℕ) : ℤ) (blockingFactor_pos D) (neg_m_le_K D)).2.2.2.2.2
    (one_lt_blockingFactor D) (scaleExponent_pos D)
theorem finite_vertex (hC : PeriodicLattice.SiteAndPlaquetteCounts) : Finite D.Vertex := by
  have h := (hC D.L D.m ((D.K : ℕ) : ℤ) (blockingFactor_pos D) (neg_m_le_K D)).2.2.1
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  have := blockingFactor_pos D
  positivity
theorem finite_face (hC : PeriodicLattice.SiteAndPlaquetteCounts) : Finite D.Face := by
  have h := (hC D.L D.m ((D.K : ℕ) : ℤ) (blockingFactor_pos D) (neg_m_le_K D)).2.2.2.1
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  have := blockingFactor_pos D
  positivity
theorem finite_edge (hC : PeriodicLattice.SiteAndPlaquetteCounts) : Finite D.Edge := by
  have := finite_vertex (D := D) hC
  have h : Function.Injective (fun b : D.Edge => (b.source, b.target)) := by
    intro b b' hb
    exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  exact Finite.of_injective _ h
theorem gaugeFieldOfPositive_positiveEdgeValues (U : D.FieldSpace) :
    PeriodicLattice.gaugeFieldOfPositive (D.positiveEdgeValues U) = U.1 := by
  classical
  funext b
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h]
    rfl
  · have h' : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left h
    rw [dif_neg h, dif_pos h']
    show (U.1 b.opposite)⁻¹ = U.1 b
    have hr := U.2.2 b.opposite (mem_univ _)
    rw [opposite_opposite] at hr
    exact hr.symm
theorem gaugeFieldOfPositive_comp_positiveEdgeValues :
    PeriodicLattice.gaugeFieldOfPositive ∘ D.positiveEdgeValues = Subtype.val :=
  funext gaugeFieldOfPositive_positiveEdgeValues
theorem positiveEdgeValues_bijective (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Function.Bijective D.positiveEdgeValues := by
  obtain ⟨-, hE, hR, -, -⟩ := latticeFacts (D := D) hC
  constructor
  · intro U V h
    apply Subtype.ext
    rw [← gaugeFieldOfPositive_positiveEdgeValues U, ← gaugeFieldOfPositive_positiveEdgeValues V, h]
  · intro g
    have hg : PeriodicLattice.gaugeFieldOfPositive g ∈
        PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := hR ▸ mem_range_self g
    refine ⟨⟨_, hg⟩, hE.injective ?_⟩
    exact gaugeFieldOfPositive_positiveEdgeValues _
theorem productTopology_eq_subtype (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    D.productTopology = (inferInstance : TopologicalSpace D.FieldSpace) := by
  obtain ⟨-, hE, -, -, -⟩ := latticeFacts (D := D) hC
  have h : TopologicalSpace.induced (Subtype.val : D.FieldSpace → _) inferInstance =
      TopologicalSpace.induced D.positiveEdgeValues inferInstance := by
    rw [← gaugeFieldOfPositive_comp_positiveEdgeValues (D := D), ← induced_compose,
      ← hE.eq_induced]
  exact h.symm
theorem comap_borel_positiveEdgeValues (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    MeasurableSpace.comap D.positiveEdgeValues
        (borel (D.PositiveEdge → ComplexMatrix2.specialUnitary)) =
      (inferInstance : MeasurableSpace D.FieldSpace) := by
  obtain ⟨-, hE, -, -, -⟩ := latticeFacts (D := D) hC
  have hb : borel (D.PositiveEdge → ComplexMatrix2.specialUnitary) =
      MeasurableSpace.comap PeriodicLattice.gaugeFieldOfPositive
        (borel (D.Edge → ComplexMatrix2)) :=
    (congrArg (@borel _) hE.eq_induced).trans borel_comap
  rw [hb, MeasurableSpace.comap_comp, gaugeFieldOfPositive_comp_positiveEdgeValues,
    ← BorelSpace.measurable_eq]
  rfl
theorem continuousForProduct_of_continuous (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    {Y : Type*} [TopologicalSpace Y] {F : D.FieldSpace → Y} (hF : Continuous F) :
    D.ContinuousForProduct F := by
  unfold MirrorData.ContinuousForProduct
  rw [productTopology_eq_subtype hC]
  exact hF
theorem fieldSpaceIsProduct (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hG : ComplexMatrix2.FiniteProductGroupStatement) : D.FieldSpaceIsProduct := by
  have hfin := (latticeFacts (D := D) hC).1
  refine ⟨finite_vertex hC, finite_edge hC, finite_face hC, positiveEdgeValues_bijective hC,
    (hG.1 _).2.1, (hG.1 _).2.2, productTopology_eq_subtype hC, comap_borel_positiveEdgeValues hC,
    gaugeFieldOfPositive_positiveEdgeValues, fun b => continuousForProduct_of_continuous hC ?_⟩
  exact ((continuous_apply b).comp continuous_subtype_val).subtype_mk _
theorem plaquetteHolonomy_mem (U : D.FieldSpace) (p : D.Face) :
    PeriodicLattice.plaquetteHolonomy U.1 p ∈ ComplexMatrix2.specialUnitary := by
  unfold PeriodicLattice.plaquetteHolonomy PeriodicLattice.pathHolonomy
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  exact U.2.1 b (mem_univ _)
theorem plaquetteEnergy_mem_Icc (hI : ComplexMatrix2.UnitaryLogarithmProperties)
    (U : D.FieldSpace) (p : D.Face) : PeriodicLattice.plaquetteCost U.1 p ∈ Icc (0 : ℝ) 2 := by
  obtain ⟨⟨t, ht, hE⟩, -⟩ := hI.2.1 _ (plaquetteHolonomy_mem U p)
  have h : (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U.1 p)).re =
      t := by
    have h' := congrArg Complex.re hE
    simpa [ComplexMatrix2.halfTrace, Complex.mul_re] using h'
  unfold PeriodicLattice.plaquetteCost
  rw [h]
  constructor <;> linarith [ht.1, ht.2]
theorem smearedObservable_eq_sum (D : MirrorData) {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype D.Face] (f : D.Torus → E) (U : D.Edge → ComplexMatrix2) :
    PeriodicLattice.smearedObservable f U =
      ∑ p : D.Face, PeriodicLattice.plaquetteCost U p • f p.barycenter :=
  finsum_eq_sum_of_fintype _
theorem wilsonAction_eq_finset_sum (D : MirrorData) [Fintype D.Face]
    (U : D.Edge → ComplexMatrix2) :
    PeriodicLattice.wilsonAction U = ∑ p : D.Face, PeriodicLattice.plaquetteCost U p :=
  finsum_eq_sum_of_fintype _
theorem continuous_smearedObservable (hC : PeriodicLattice.SiteAndPlaquetteCounts) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : D.Torus → E) :
    Continuous fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1 := by
  have := finite_face (D := D) hC
  have := Fintype.ofFinite D.Face
  have h : (fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) = fun U =>
      ∑ p : D.Face, PeriodicLattice.plaquetteCost U.1 p • f p.barycenter :=
    funext fun U => smearedObservable_eq_sum D f U.1
  rw [h]
  exact continuous_finsetSum _ fun p _ =>
    ((continuous_plaquetteEnergy p).comp continuous_subtype_val).smul continuous_const
theorem isBoundedFun_smearedObservable (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : D.Torus → E) :
    TestFunctions.IsBoundedFun fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1 := by
  have := finite_face (D := D) hC
  have := Fintype.ofFinite D.Face
  refine ⟨∑ p : D.Face, 2 * ‖f p.barycenter‖, fun U => ?_⟩
  show ‖PeriodicLattice.smearedObservable f U.1‖ ≤ _
  rw [smearedObservable_eq_sum D]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have h := plaquetteEnergy_mem_Icc hI U p
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h.1]
  exact mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
theorem smearedObservable_im (hC : PeriodicLattice.SiteAndPlaquetteCounts) (f : D.Torus → ℂ)
    (hf : ∀ x, (f x).im = 0) (U : D.FieldSpace) :
    (PeriodicLattice.smearedObservable f U.1).im = 0 := by
  have := finite_face (D := D) hC
  have := Fintype.ofFinite D.Face
  rw [smearedObservable_eq_sum D, Complex.im_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp [hf]
theorem continuous_wilsonAction (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Continuous fun U : D.Edge → ComplexMatrix2 => PeriodicLattice.wilsonAction U := by
  have := finite_face (D := D) hC
  have := Fintype.ofFinite D.Face
  have h : (fun U : D.Edge → ComplexMatrix2 => PeriodicLattice.wilsonAction U) = fun U =>
      ∑ p : D.Face, PeriodicLattice.plaquetteCost U p :=
    funext (wilsonAction_eq_finset_sum D)
  rw [h]
  exact continuous_finsetSum _ fun p _ => continuous_plaquetteEnergy p
theorem continuous_boltzmannWeight (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Continuous fun U : D.Edge → ComplexMatrix2 => PeriodicLattice.boltzmannWeight D.coupling U :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction hC))
theorem wilsonAction_mem_bounds (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) (U : D.FieldSpace) :
    0 ≤ PeriodicLattice.wilsonAction U.1 ∧
      PeriodicLattice.wilsonAction U.1 ≤ 2 * (D.faceCount : ℝ) := by
  have := finite_face (D := D) hC
  have := Fintype.ofFinite D.Face
  rw [wilsonAction_eq_finset_sum D]
  refine ⟨Finset.sum_nonneg fun p _ => (plaquetteEnergy_mem_Icc hI U p).1, ?_⟩
  calc ∑ p : D.Face, PeriodicLattice.plaquetteCost U.1 p
      ≤ ∑ _p : D.Face, (2 : ℝ) :=
        Finset.sum_le_sum fun p _ => (plaquetteEnergy_mem_Icc hI U p).2
    _ = 2 * (D.faceCount : ℝ) := by
        simp [MirrorData.faceCount, Nat.card_eq_fintype_card, mul_comm]
theorem boltzmannWeight_bounds (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) (U : D.FieldSpace) :
    Real.exp (-2 * D.coupling * (D.faceCount : ℝ)) ≤
        PeriodicLattice.boltzmannWeight D.coupling U.1 ∧
      PeriodicLattice.boltzmannWeight D.coupling U.1 ≤ 1 := by
  obtain ⟨h0, h1⟩ := wilsonAction_mem_bounds hC hI U
  have hβ := D.coupling_pos
  unfold PeriodicLattice.boltzmannWeight
  constructor
  · apply Real.exp_le_exp.2
    nlinarith
  · apply Real.exp_le_one_iff.2
    nlinarith
theorem gaugeFieldOfPositive_mem (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (g : D.PositiveEdge → ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive g ∈
      PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) :=
  (latticeFacts (D := D) hC).2.2.1 ▸ mem_range_self g
theorem measurable_gaugeFieldOfPositive (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (D.PositiveEdge → ComplexMatrix2.specialUnitary) → D.Edge → ComplexMatrix2) :=
  (latticeFacts (D := D) hC).2.1.continuous.measurable
instance instIsProbabilityGaugeFieldHaar :
    IsProbabilityMeasure (PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ)) := by
  unfold PeriodicLattice.gaugeFieldHaar ComplexMatrix2.haarPi
  infer_instance
theorem integrable_boltzmannWeight_comp (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    Integrable
      (fun g => PeriodicLattice.boltzmannWeight D.coupling (PeriodicLattice.gaugeFieldOfPositive g))
      (PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ)) := by
  have hc : Continuous fun g : D.PositiveEdge → ComplexMatrix2.specialUnitary =>
      PeriodicLattice.boltzmannWeight D.coupling (PeriodicLattice.gaugeFieldOfPositive g) :=
    (continuous_boltzmannWeight hC).comp (latticeFacts (D := D) hC).2.1.continuous
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
  have h := boltzmannWeight_bounds hC hI ⟨_, gaugeFieldOfPositive_mem hC g⟩
  have hn : 0 ≤ PeriodicLattice.boltzmannWeight D.coupling
      (PeriodicLattice.gaugeFieldOfPositive g) :=
    (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact h.2
theorem partitionFunction_eq_integral (hC : PeriodicLattice.SiteAndPlaquetteCounts) :
    PeriodicLattice.partitionFunction D.L D.m D.K D.coupling =
      ∫ g, PeriodicLattice.boltzmannWeight D.coupling (PeriodicLattice.gaugeFieldOfPositive g)
        ∂PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ) := by
  unfold PeriodicLattice.partitionFunction PeriodicLattice.productHaarMeasure
  exact integral_map (measurable_gaugeFieldOfPositive hC).aemeasurable
    (continuous_boltzmannWeight hC).aestronglyMeasurable
theorem partitionFunction_bounds (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    Real.exp (-2 * D.coupling * (D.faceCount : ℝ)) ≤
        PeriodicLattice.partitionFunction D.L D.m D.K D.coupling ∧
      PeriodicLattice.partitionFunction D.L D.m D.K D.coupling ≤ 1 := by
  rw [partitionFunction_eq_integral hC]
  have hint := integrable_boltzmannWeight_comp (D := D) hC hI
  constructor
  · calc Real.exp (-2 * D.coupling * (D.faceCount : ℝ))
        = ∫ _g, Real.exp (-2 * D.coupling * (D.faceCount : ℝ))
            ∂PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun g =>
          (boltzmannWeight_bounds hC hI ⟨_, gaugeFieldOfPositive_mem hC g⟩).1
  · calc _ ≤ ∫ _g, (1 : ℝ) ∂PeriodicLattice.gaugeFieldHaar D.L D.m ((D.K : ℕ) : ℤ) :=
          integral_mono hint (integrable_const _) fun g =>
            (boltzmannWeight_bounds hC hI ⟨_, gaugeFieldOfPositive_mem hC g⟩).2
      _ = 1 := by simp
theorem integrable_boltzmannWeight (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    Integrable (PeriodicLattice.boltzmannWeight D.coupling)
      (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) := by
  unfold PeriodicLattice.productHaarMeasure
  exact (integrable_map_measure (continuous_boltzmannWeight hC).aestronglyMeasurable
    (measurable_gaugeFieldOfPositive hC).aemeasurable).2 (integrable_boltzmannWeight_comp hC hI)
theorem isProbabilityMeasure_wilsonGibbsMeasure (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) := by
  have hZ : 0 < PeriodicLattice.partitionFunction D.L D.m D.K D.coupling :=
    (Real.exp_pos _).trans_le (partitionFunction_bounds hC hI).1
  constructor
  unfold PeriodicLattice.wilsonGibbsMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_boltzmannWeight hC hI)
      (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le)]
  change (ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.coupling))⁻¹ *
    ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.coupling) = 1
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
theorem isProbabilityMeasure_gibbsMeasureOnFields
    (hC : PeriodicLattice.SiteAndPlaquetteCounts) (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    IsProbabilityMeasure D.gibbsMeasureOnFields := by
  have hprob := isProbabilityMeasure_wilsonGibbsMeasure (D := D) hC hI
  have hS : MeasurableSet (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :=
    (latticeFacts (D := D) hC).2.2.2.1.isClosed.measurableSet
  have hcompl : PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
      (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))ᶜ = 0 := by
    unfold PeriodicLattice.productHaarMeasure
    rw [Measure.map_apply (measurable_gaugeFieldOfPositive hC) hS.compl]
    have h : (PeriodicLattice.gaugeFieldOfPositive :
        (D.PositiveEdge → ComplexMatrix2.specialUnitary) → D.Edge → ComplexMatrix2) ⁻¹'
        (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))ᶜ = ∅ := by
      ext g
      simpa using gaugeFieldOfPositive_mem hC g
    rw [h, measure_empty]
  have hW : PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling
      (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ))ᶜ = 0 := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hcompl, smul_zero]
  constructor
  unfold MirrorData.gibbsMeasureOnFields
  rw [(MeasurableEmbedding.subtype_coe hS).comap_apply, image_univ, Subtype.range_coe]
  exact (prob_compl_eq_zero_iff hS).1 hW
theorem energiesBoundedAndMeasureProbability (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) : D.EnergiesBoundedAndMeasureProbability := by
  have hZ := partitionFunction_bounds (D := D) hC hI
  refine ⟨fun p => ⟨continuousForProduct_of_continuous hC
      ((continuous_plaquetteEnergy p).comp continuous_subtype_val),
      fun U => plaquetteEnergy_mem_Icc hI U p⟩,
    fun f => ⟨continuousForProduct_of_continuous hC (continuous_smearedObservable hC f),
      isBoundedFun_smearedObservable hC hI f⟩,
    fun f => ⟨continuousForProduct_of_continuous hC (continuous_smearedObservable hC f),
      isBoundedFun_smearedObservable hC hI f, fun hf U => smearedObservable_im hC f hf U⟩,
    continuousForProduct_of_continuous hC
      ((continuous_wilsonAction hC).comp continuous_subtype_val),
    continuousForProduct_of_continuous hC
      ((continuous_boltzmannWeight hC).comp continuous_subtype_val),
    wilsonAction_mem_bounds hC hI, hZ.1, hZ.2, (Real.exp_pos _).trans_le hZ.1,
    integrable_boltzmannWeight hC hI, isProbabilityMeasure_wilsonGibbsMeasure hC hI,
    isProbabilityMeasure_gibbsMeasureOnFields hC hI⟩
end OfData
theorem holds (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hG : ComplexMatrix2.FiniteProductGroupStatement)
    (hH : ComplexMatrix2.HaarExpChartProperties)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) : Statement := fun _ =>
  ⟨OfData.fieldSpaceIsProduct hC hG, relabelInvert_measurePreserving hH,
    OfData.energiesBoundedAndMeasureProbability hC hI⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies
end
